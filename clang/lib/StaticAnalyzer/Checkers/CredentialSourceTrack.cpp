#include "Yaml.h"
#include "clang/AST/Attr.h"
#include "clang/Basic/Builtins.h"
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Checkers/Taint.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallDescription.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/YAMLTraits.h"

#include <limits>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

#include<sstream>
#include<iostream>
#include<fstream>
#include<string.h>
#include<map>

#define DEBUG_TYPE "taint-checker"

using namespace clang;
using namespace ento;
using namespace taint;

using llvm::ImmutableSet;

std::string cs_debug_output_path = "";
std::string cs_other_output_path = "";

namespace {

class CredentialSourceTrackChecker;

constexpr llvm::StringLiteral MsgCustomSinkFile =
    "Credential data is obtained by an external file";

constexpr llvm::StringLiteral MsgCustomSinkEnv =
    "Credential data is obtained by an environment variable";

constexpr llvm::StringLiteral MsgCustomSinkArg =
    "Credential data is obtained by a program argument";

constexpr llvm::StringLiteral MsgCustomSinkConst =
    "Credential data is obtained by a constant string";

constexpr llvm::StringLiteral MsgCustomSinkOther =
    "Credential data is obtained from external input";

using ArgIdxTy = int;
using ArgVecTy = llvm::SmallVector<ArgIdxTy, 2>;


constexpr ArgIdxTy ReturnValueIndex{-1};


static ArgIdxTy fromArgumentCount(unsigned Count) {
  assert(Count <=
             static_cast<std::size_t>(std::numeric_limits<ArgIdxTy>::max()) &&
         "ArgIdxTy is not large enough to represent the number of arguments.");
  return Count;
}


bool isStdin(SVal Val, const ASTContext &ACtx) {
  const auto *SymReg = dyn_cast_or_null<SymbolicRegion>(Val.getAsRegion());
  if (!SymReg)
    return false;

  const auto *DeclReg =
      dyn_cast_or_null<DeclRegion>(SymReg->getSymbol()->getOriginRegion());
  if (!DeclReg)
    return false;

  if (const auto *D = dyn_cast_or_null<VarDecl>(DeclReg->getDecl())) {
    D = D->getCanonicalDecl();
    if (D->getName() == "stdin" && D->hasExternalStorage() && D->isExternC()) {
      const QualType FILETy = ACtx.getFILEType().getCanonicalType();
      const QualType Ty = D->getType().getCanonicalType();

      if (Ty->isPointerType())
        return Ty->getPointeeType() == FILETy;
    }
  }
  return false;
}

SVal getPointeeOf(ProgramStateRef State, Loc LValue) {
  const QualType ArgTy = LValue.getType(State->getStateManager().getContext());
  if (!ArgTy->isPointerType() || !ArgTy->getPointeeType()->isVoidType())
    return State->getSVal(LValue);

  return State->getSVal(LValue, State->getStateManager().getContext().CharTy);
}

std::optional<SVal> getPointeeOf(ProgramStateRef State, SVal Arg) {
  if (auto LValue = Arg.getAs<Loc>())
    return getPointeeOf(State, *LValue);
  return std::nullopt;
}

std::optional<SVal> getTaintedPointeeOrPointer(ProgramStateRef State, SVal Arg, TaintTagType tag) {
  if (auto Pointee = getPointeeOf(State, Arg))
    if (isTainted(State, *Pointee, tag)) // FIXME: isTainted(...) ? Pointee : None;
      return Pointee;

  if (isTainted(State, Arg, tag))
    return Arg;
  return std::nullopt;
}

std::optional<SVal> getPointeeOrPointer(ProgramStateRef State, SVal Arg) {
  if (auto Pointee = getPointeeOf(State, Arg)){
    return Pointee;
  }else{
    return Arg;
  }
}

bool isTaintedOrPointsToTainted(ProgramStateRef State, SVal ExprSVal, TaintTagType tag=TaintTagNone) {
  
  if (tag == TaintTagNone){
    bool res = getTaintedPointeeOrPointer(State, ExprSVal, TaintTagCredSrcFile).has_value();
    if(res)
      return res;
    res = getTaintedPointeeOrPointer(State, ExprSVal,  TaintTagCredSrcEnv).has_value();
    if(res)
      return res;
    res = getTaintedPointeeOrPointer(State, ExprSVal, TaintTagCredSrcOptarg).has_value();
    if(res)
      return res;
    res = getTaintedPointeeOrPointer(State, ExprSVal, TaintTagCredSrcConst).has_value();
    if(res)
      return res;
    res = getTaintedPointeeOrPointer(State, ExprSVal, TaintTagCredSrcOtherInput).has_value();
    if(res)
      return res;
  }
  return getTaintedPointeeOrPointer(State, ExprSVal, tag).has_value();
}

/// Helps in printing taint diagnostics.
/// Marks the incoming parameters of a function interesting (to be printed)
/// when the return value, or the outgoing parameters are tainted.
const NoteTag *taintOriginTrackerTag(CheckerContext &C,
                                     std::vector<SymbolRef> TaintedSymbols,
                                     std::vector<ArgIdxTy> TaintedArgs,
                                     const LocationContext *CallLocation) {
  return C.getNoteTag([TaintedSymbols = std::move(TaintedSymbols),
                       TaintedArgs = std::move(TaintedArgs), CallLocation](
                          PathSensitiveBugReport &BR) -> std::string {
    SmallString<256> Msg;
    // We give diagnostics only for taint related reports
    if (!BR.isInteresting(CallLocation) ||
        BR.getBugType().getCategory() != categories::TaintedData) {
      return "";
    }
    if (TaintedSymbols.empty())
      return "Taint originated here";

    for (auto Sym : TaintedSymbols) {
      BR.markInteresting(Sym);
    }
    LLVM_DEBUG(for (auto Arg
                    : TaintedArgs) {
      llvm::dbgs() << "Taint Propagated from argument " << Arg + 1 << "\n";
    });
    return "";
  });
}


std::string str2lower(std::string s){
  for (auto& x : s) {
    x = tolower(x);
  }
  return s;

}


bool isConstVar(const Expr *E) {
  
  const Expr* CE = E;
  while(1){
    if (const auto *ICE = dyn_cast_or_null<ImplicitCastExpr>(CE)){
      CE = ICE->getSubExpr();
    }else if(const auto * SL = dyn_cast_or_null<StringLiteral>(CE)){
      return true;
    }
    // else if(const auto *SE = dyn_cast_or_null<DeclRefExpr>(CE)){
      
    // }
    else{
      return false;
    }
  }

  return false;
}

bool isFileVar(const Expr *E) {
  
  const Expr* CE = E;
  while(1){
    if (const auto *ICE = dyn_cast_or_null<ImplicitCastExpr>(CE)){
      CE = ICE->getSubExpr();
    }
    else if(const auto *DRE = dyn_cast_or_null<DeclRefExpr>(CE)){
      if(const auto *VE = DRE->getDecl()){
          std::string var_type = str2lower(VE->getType().getAsString());
          // llvm::errs() << var_type << "\n";
          if (var_type.find("file") != std::string::npos){
              return true;
          }
      }
      break;
    }
    else{
      break;
    }
  }

  return false;
}

bool isOptargVar(const Expr *E) {
    const Expr *AE = E;
    // llvm::dbgs() << "\n---isOptargVar---\n";

    while(1){
      if(const auto *ICE = dyn_cast_or_null<ImplicitCastExpr>(AE)){
        AE = ICE->getSubExpr();
      }else if (const auto *DRE = dyn_cast_or_null<DeclRefExpr>(AE)){
        if(const auto *VE = DRE->getDecl()){
            std::string var_name = str2lower(VE->getNameAsString());
            // llvm::dbgs() << var_name;
            // if (var_name.find("user") != std::string::npos || var_name.find("pass") != std::string::npos){
            if (var_name.find("optarg") != std::string::npos){
                return true;
            }
        }
        break;
      }else{
        break;
      }
    }
    
    return false;
}

bool isStdinVar(const Expr *E) {
    const Expr *AE = E;
    // llvm::dbgs() << "\n---isStdinVar---\n";

    while(1){
      if(const auto *ICE = dyn_cast_or_null<ImplicitCastExpr>(AE)){
        AE = ICE->getSubExpr();
      }else if (const auto *DRE = dyn_cast_or_null<DeclRefExpr>(AE)){
        if(const auto *VE = DRE->getDecl()){
            std::string var_name = str2lower(VE->getNameAsString());
            // llvm::dbgs() << var_name;
            // if (var_name.find("user") != std::string::npos || var_name.find("pass") != std::string::npos){
            if (var_name.find("stdin") != std::string::npos){
                return true;
            }
        }
        break;
      }else{
        break;
      }
    }

    return false;
}

bool isCredentialVar(const Expr *E) {
    const Expr *AE = E;
    while(1){
      if(const auto *ME = dyn_cast_or_null<MemberExpr>(AE)){
        if(const auto *VE = ME->getMemberDecl()){
            std::string var_name = str2lower(VE->getNameAsString());
            if (var_name.find("pass") != std::string::npos || var_name.find("account") != std::string::npos || var_name.find("secret") != std::string::npos || var_name.find("credential") != std::string::npos){
                return true;
            }
        }
        AE = ME->getBase();
      }else if(const auto *ICE = dyn_cast_or_null<ImplicitCastExpr>(AE)){
        AE = ICE->getSubExpr();
      }else if(const auto *DRE = dyn_cast_or_null<DeclRefExpr>(AE)){
        if(const auto *VE = DRE->getDecl()){
            std::string var_name = str2lower(VE->getNameAsString());
            if (var_name.find("pass") != std::string::npos || var_name.find("account") != std::string::npos || var_name.find("secret") != std::string::npos || var_name.find("credential") != std::string::npos){
                return true;
            }
        }
        break;
      }else{
        break;
      }
    }

    return false;
}

/// Helps in printing taint diagnostics.
/// Marks the function interesting (to be printed)
/// when the return value, or the outgoing parameters are tainted.
const NoteTag *taintPropagationExplainerTag(
    CheckerContext &C, std::vector<SymbolRef> TaintedSymbols,
    std::vector<ArgIdxTy> TaintedArgs, const LocationContext *CallLocation) {
  assert(TaintedSymbols.size() == TaintedArgs.size());
  return C.getNoteTag([TaintedSymbols = std::move(TaintedSymbols),
                       TaintedArgs = std::move(TaintedArgs), CallLocation](
                          PathSensitiveBugReport &BR) -> std::string {
    SmallString<256> Msg;
    llvm::raw_svector_ostream Out(Msg);
    // We give diagnostics only for taint related reports
    if (TaintedSymbols.empty() ||
        BR.getBugType().getCategory() != categories::TaintedData) {
      return "";
    }
    int nofTaintedArgs = 0;
    for (auto [Idx, Sym] : llvm::enumerate(TaintedSymbols)) {
      if (BR.isInteresting(Sym)) {
        BR.markInteresting(CallLocation);
        if (TaintedArgs[Idx] != ReturnValueIndex) {
          LLVM_DEBUG(llvm::dbgs() << "Taint Propagated to argument "
                                  << TaintedArgs[Idx] + 1 << "\n");
          if (nofTaintedArgs == 0)
            Out << "Taint propagated to the ";
          else
            Out << ", ";
          Out << TaintedArgs[Idx] + 1
              << llvm::getOrdinalSuffix(TaintedArgs[Idx] + 1) << " argument";
          nofTaintedArgs++;
        } else {
          LLVM_DEBUG(llvm::dbgs() << "Taint Propagated to return value.\n");
          Out << "Taint propagated to the return value";
        }
      }
    }
    return std::string(Out.str());
  });
}


class ArgSet {
public:
  ArgSet() = default;
  ArgSet(ArgVecTy &&DiscreteArgs, std::optional<ArgIdxTy> VariadicIndex = std::nullopt)
      : DiscreteArgs(std::move(DiscreteArgs)),
        VariadicIndex(std::move(VariadicIndex)) {}

  bool contains(ArgIdxTy ArgIdx) const {
    if (llvm::is_contained(DiscreteArgs, ArgIdx))
      return true;

    return VariadicIndex && ArgIdx >= *VariadicIndex;
  }

  bool isEmpty() const { return DiscreteArgs.empty() && !VariadicIndex; }

private:
  ArgVecTy DiscreteArgs;
  std::optional<ArgIdxTy> VariadicIndex;
};


class CredentialSourceTrackRule {
  ArgSet SinkArgs;
  ArgSet SourceArgs;
  ArgSet FilterArgs;
  ArgSet PropSrcArgs;
  ArgSet PropDstArgs;


  std::optional<TaintTagType> SrcMsg;
  std::optional<StringRef> SinkMsg;

  CredentialSourceTrackRule() = default;

  CredentialSourceTrackRule(ArgSet &&Sink, ArgSet &&Source, ArgSet &&Filter, ArgSet &&Src, ArgSet &&Dst,
                   std::optional<TaintTagType> SrcMsg = TaintTagNone,
                   std::optional<StringRef> SinkMsg = std::nullopt)
      : SinkArgs(std::move(Sink)), SourceArgs(std::move(Source)), 
        FilterArgs(std::move(Filter)),
        PropSrcArgs(std::move(Src)), PropDstArgs(std::move(Dst)),
        SrcMsg(SrcMsg), SinkMsg(SinkMsg) {}

public:
  static CredentialSourceTrackRule Sink(ArgSet &&SinkArgs,
                               std::optional<StringRef> Msg = std::nullopt) {
    return {std::move(SinkArgs), {}, {}, {}, {}, TaintTagNone, Msg};
  }

  static CredentialSourceTrackRule Filter(ArgSet &&FilterArgs) {
    return {{}, {}, std::move(FilterArgs), {}, {}};
  }

  static CredentialSourceTrackRule Source(ArgSet &&SourceArgs, std::optional<TaintTagType> Msg = TaintTagNone) {
    return {{}, std::move(SourceArgs), {}, {}, {}, Msg, std::nullopt};
  }

  static CredentialSourceTrackRule Prop(ArgSet &&SrcArgs, ArgSet &&DstArgs) {
    return {{}, {}, {}, std::move(SrcArgs), std::move(DstArgs)};
  }

  static CredentialSourceTrackRule
  SinkProp(ArgSet &&SinkArgs, ArgSet &&SrcArgs, ArgSet &&DstArgs,
           std::optional<StringRef> Msg = std::nullopt) {
    return {
        std::move(SinkArgs), {}, {}, std::move(SrcArgs), std::move(DstArgs), TaintTagNone, Msg};
  }

  void process(const CredentialSourceTrackChecker &Checker, const CallEvent &Call,
               CheckerContext &C) const;

  static const Expr *GetArgExpr(ArgIdxTy ArgIdx, const CallEvent &Call) {
    return ArgIdx == ReturnValueIndex ? Call.getOriginExpr()
                                      : Call.getArgExpr(ArgIdx);
  };

  static bool UntrustedEnv(CheckerContext &C);
};

using RuleLookupTy = CallDescriptionMap<CredentialSourceTrackRule>;


struct TaintConfiguration {
  using NameScopeArgs = std::tuple<std::string, std::string, ArgVecTy>;
  enum class VariadicType { None, Src, Dst };

  struct Common {
    std::string Name;
    std::string Scope;
  };

  struct Sink : Common {
    ArgVecTy SinkArgs;
  };
  struct Source : Common {
    ArgVecTy SourceArgs;
    TaintTagType Type;
  };

  struct Filter : Common {
    ArgVecTy FilterArgs;
    TaintTagType Type;
  };

  struct Propagation : Common {
    ArgVecTy SrcArgs;
    ArgVecTy DstArgs;
    VariadicType VarType;
    ArgIdxTy VarIndex;
  };

  std::vector<Propagation> Propagations;
  std::vector<Filter> Filters;
  std::vector<Sink> Sinks;
  std::vector<Source> Sources;

  TaintConfiguration() = default;
  TaintConfiguration(const TaintConfiguration &) = default;
  TaintConfiguration(TaintConfiguration &&) = default;
  TaintConfiguration &operator=(const TaintConfiguration &) = default;
  TaintConfiguration &operator=(TaintConfiguration &&) = default;
};

struct CredentialSourceTrackRuleParser {
  CredentialSourceTrackRuleParser(CheckerManager &Mgr) : Mgr(Mgr) {}
  
  using RulesContTy = std::vector<std::pair<CallDescription, CredentialSourceTrackRule>>;
  RulesContTy parseConfiguration(const std::string &Option,
                                 TaintConfiguration &&Config) const;

private:
  using NamePartsTy = llvm::SmallVector<StringRef, 2>;

  void validateArgVector(const std::string &Option, const ArgVecTy &Args) const;

  template <typename Config> static NamePartsTy parseNameParts(const Config &C);

  template <typename Config>
  static void consumeRulesFromConfig(const Config &C, CredentialSourceTrackRule &&Rule,
                                     RulesContTy &Rules);

  void parseConfig(const std::string &Option, TaintConfiguration::Sink &&P,
                   RulesContTy &Rules) const;
  void parseConfig(const std::string &Option, TaintConfiguration::Source &&P,
                   RulesContTy &Rules) const;
  void parseConfig(const std::string &Option, TaintConfiguration::Filter &&P,
                   RulesContTy &Rules) const;
  void parseConfig(const std::string &Option,
                   TaintConfiguration::Propagation &&P,
                   RulesContTy &Rules) const;

  CheckerManager &Mgr;
};

class CredentialSourceTrackChecker : public Checker<check::PreCall, check::PostCall,
                                            check::PreStmt<BinaryOperator>,
                                            check::PostStmt<BinaryOperator>> {
public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;

  void checkPreStmt(const BinaryOperator *BO, CheckerContext &C) const;
  void checkPostStmt(const BinaryOperator *BO, CheckerContext &C) const;

  void printState(raw_ostream &Out, ProgramStateRef State, const char *NL,
                  const char *Sep) const override;

  bool generateReportIfTainted(const Expr *E, StringRef Msg,
                               CheckerContext &C) const;
  void isVulnerableVar(const Expr *E, const ProgramStateRef &State, CheckerContext &C) const;


private:
  const BugType BT{this, "Use of Untrusted Data", categories::TaintedData};

  void initTaintRules(CheckerContext &C) const;

  mutable std::optional<RuleLookupTy> StaticTaintRules;
  mutable std::optional<RuleLookupTy> DynamicTaintRules;
};
} // end of anonymous namespace

/// YAML serialization mapping.
LLVM_YAML_IS_SEQUENCE_VECTOR(TaintConfiguration::Sink)
LLVM_YAML_IS_SEQUENCE_VECTOR(TaintConfiguration::Source)
LLVM_YAML_IS_SEQUENCE_VECTOR(TaintConfiguration::Filter)
LLVM_YAML_IS_SEQUENCE_VECTOR(TaintConfiguration::Propagation)

namespace llvm {
namespace yaml {
template <> struct MappingTraits<TaintConfiguration> {
  static void mapping(IO &IO, TaintConfiguration &Config) {
    IO.mapOptional("Propagations", Config.Propagations);
    IO.mapOptional("Filters", Config.Filters);
    IO.mapOptional("Sinks", Config.Sinks);
    IO.mapOptional("Sources", Config.Sources);
  }
};

template <> struct MappingTraits<TaintConfiguration::Sink> {
  static void mapping(IO &IO, TaintConfiguration::Sink &Sink) {
    IO.mapRequired("Name", Sink.Name);
    IO.mapOptional("Scope", Sink.Scope);
    IO.mapRequired("Args", Sink.SinkArgs);
  }
};

template <> struct MappingTraits<TaintConfiguration::Source> {
  static void mapping(IO &IO, TaintConfiguration::Source &Source) {
    IO.mapRequired("Name", Source.Name);
    IO.mapOptional("Scope", Source.Scope);
    IO.mapRequired("Args", Source.SourceArgs);
    IO.mapRequired("Type", Source.Type);
  }
};

template <> struct MappingTraits<TaintConfiguration::Filter> {
  static void mapping(IO &IO, TaintConfiguration::Filter &Filter) {
    IO.mapRequired("Name", Filter.Name);
    IO.mapOptional("Scope", Filter.Scope);
    IO.mapRequired("Args", Filter.FilterArgs);
    IO.mapRequired("Type", Filter.Type);
  }
};

template <> struct MappingTraits<TaintConfiguration::Propagation> {
  static void mapping(IO &IO, TaintConfiguration::Propagation &Propagation) {
    IO.mapRequired("Name", Propagation.Name);
    IO.mapOptional("Scope", Propagation.Scope);
    IO.mapOptional("SrcArgs", Propagation.SrcArgs);
    IO.mapOptional("DstArgs", Propagation.DstArgs);
    IO.mapOptional("VariadicType", Propagation.VarType);
    IO.mapOptional("VariadicIndex", Propagation.VarIndex);
  }
};

template <> struct ScalarEnumerationTraits<TaintConfiguration::VariadicType> {
  static void enumeration(IO &IO, TaintConfiguration::VariadicType &Value) {
    IO.enumCase(Value, "None", TaintConfiguration::VariadicType::None);
    IO.enumCase(Value, "Src", TaintConfiguration::VariadicType::Src);
    IO.enumCase(Value, "Dst", TaintConfiguration::VariadicType::Dst);
  }
};
} // namespace yaml
} // namespace llvm

/// A set which is used to pass information from call pre-visit instruction
/// to the call post-visit. The values are signed integers, which are either
/// ReturnValueIndex, or indexes of the pointer/reference argument, which
/// points to data, which should be tainted on return.
REGISTER_MAP_WITH_PROGRAMSTATE(TaintArgsOnPostVisit, const LocationContext *,
                               ImmutableSet<ArgIdxTy>)
REGISTER_SET_FACTORY_WITH_PROGRAMSTATE(ArgIdxFactory, ArgIdxTy)
REGISTER_SET_FACTORY_WITH_PROGRAMSTATE(TaintTagSet, TaintTagType)
REGISTER_MAP_WITH_PROGRAMSTATE(TaintTagsOnPostVisit, const LocationContext *,
                               TaintTagSet)

void CredentialSourceTrackRuleParser::validateArgVector(const std::string &Option,
                                               const ArgVecTy &Args) const {
  for (ArgIdxTy Arg : Args) {
    if (Arg < ReturnValueIndex) {
      Mgr.reportInvalidCheckerOptionValue(
          Mgr.getChecker<CredentialSourceTrackChecker>(), Option,
          "an argument number for propagation rules greater or equal to -1");
    }
  }
}

template <typename Config>
CredentialSourceTrackRuleParser::NamePartsTy
CredentialSourceTrackRuleParser::parseNameParts(const Config &C) {
  NamePartsTy NameParts;
  if (!C.Scope.empty()) {
    // If the Scope argument contains multiple "::" parts, those are considered
    // namespace identifiers.
    StringRef{C.Scope}.split(NameParts, "::", /*MaxSplit*/ -1,
                             /*KeepEmpty*/ false);
  }
  NameParts.emplace_back(C.Name);
  return NameParts;
}

template <typename Config>
void CredentialSourceTrackRuleParser::consumeRulesFromConfig(const Config &C,
                                                    CredentialSourceTrackRule &&Rule,
                                                    RulesContTy &Rules) {
  NamePartsTy NameParts = parseNameParts(C);
  Rules.emplace_back(CallDescription(NameParts), std::move(Rule));
}

void CredentialSourceTrackRuleParser::parseConfig(const std::string &Option,
                                         TaintConfiguration::Sink &&S,
                                         RulesContTy &Rules) const {
  validateArgVector(Option, S.SinkArgs);
  consumeRulesFromConfig(S, CredentialSourceTrackRule::Sink(std::move(S.SinkArgs)),
                         Rules);
}

void CredentialSourceTrackRuleParser::parseConfig(const std::string &Option,
                                         TaintConfiguration::Source &&S,
                                         RulesContTy &Rules) const {
  validateArgVector(Option, S.SourceArgs);
  consumeRulesFromConfig(S, CredentialSourceTrackRule::Source(std::move(S.SourceArgs), std::move(S.Type)),
                         Rules);
}

void CredentialSourceTrackRuleParser::parseConfig(const std::string &Option,
                                         TaintConfiguration::Filter &&S,
                                         RulesContTy &Rules) const {
  validateArgVector(Option, S.FilterArgs);
  consumeRulesFromConfig(S, CredentialSourceTrackRule::Filter(std::move(S.FilterArgs)),
                         Rules);
}

void CredentialSourceTrackRuleParser::parseConfig(const std::string &Option,
                                         TaintConfiguration::Propagation &&P,
                                         RulesContTy &Rules) const {
  validateArgVector(Option, P.SrcArgs);
  validateArgVector(Option, P.DstArgs);
  bool IsSrcVariadic = P.VarType == TaintConfiguration::VariadicType::Src;
  bool IsDstVariadic = P.VarType == TaintConfiguration::VariadicType::Dst;
  std::optional<ArgIdxTy> JustVarIndex = P.VarIndex;

  ArgSet SrcDesc(std::move(P.SrcArgs),
                 IsSrcVariadic ? JustVarIndex : std::nullopt);
  ArgSet DstDesc(std::move(P.DstArgs),
                 IsDstVariadic ? JustVarIndex : std::nullopt);

  consumeRulesFromConfig(
      P, CredentialSourceTrackRule::Prop(std::move(SrcDesc), std::move(DstDesc)), Rules);
}

CredentialSourceTrackRuleParser::RulesContTy
CredentialSourceTrackRuleParser::parseConfiguration(const std::string &Option,
                                           TaintConfiguration &&Config) const {

  RulesContTy Rules;

  for (auto &F : Config.Filters)
    parseConfig(Option, std::move(F), Rules);

  for (auto &S : Config.Sinks)
    parseConfig(Option, std::move(S), Rules);

  for (auto &S : Config.Sources)
    parseConfig(Option, std::move(S), Rules);

  for (auto &P : Config.Propagations)
    parseConfig(Option, std::move(P), Rules);

  return Rules;
}

void CredentialSourceTrackChecker::initTaintRules(CheckerContext &C) const {
  if (StaticTaintRules || DynamicTaintRules)
    return;

  using RulesConstructionTy =
      std::vector<std::pair<CallDescription, CredentialSourceTrackRule>>;
  using TR = CredentialSourceTrackRule;

  const Builtin::Context &BI = C.getASTContext().BuiltinInfo;

  RulesConstructionTy GlobalCRules{
      // Sources
      {{{"fdopen"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcFile)},
      {{{"fopen"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcFile)},
      {{{"freopen"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcFile)},
      {{{"open"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcFile)},

      {{{"getenv"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcEnv)},

      {{{"getpass"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"getch"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"getchar"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"getchar_unlocked"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"gets"}}, TR::Source({{0}, ReturnValueIndex}, TaintTagCredSrcOtherInput)},
      {{{"gets_s"}}, TR::Source({{0}, ReturnValueIndex}, TaintTagCredSrcOtherInput)},
      {{{"scanf"}}, TR::Source({{}, 1}, TaintTagCredSrcOtherInput)},
      {{{"scanf_s"}}, TR::Source({{}, {1}}, TaintTagCredSrcOtherInput)},
      {{{"wgetch"}}, TR::Source({{}, ReturnValueIndex}, TaintTagCredSrcOtherInput)},
      {{{"_IO_getc"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"getcwd"}}, TR::Source({{0, ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"getwd"}}, TR::Source({{0, ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"readlink"}}, TR::Source({{1, ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"readlinkat"}}, TR::Source({{2, ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"get_current_dir_name"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"gethostname"}}, TR::Source({{0}}, TaintTagCredSrcOtherInput)},
      {{{"getnameinfo"}}, TR::Source({{2, 4}}, TaintTagCredSrcOtherInput)},
      {{{"getseuserbyname"}}, TR::Source({{1, 2}}, TaintTagCredSrcOtherInput)},
      {{{"getgroups"}}, TR::Source({{1, ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"getlogin"}}, TR::Source({{ReturnValueIndex}}, TaintTagCredSrcOtherInput)},
      {{{"getlogin_r"}}, TR::Source({{0}}, TaintTagCredSrcOtherInput)},

      // Props
      {{{"accept"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"atoi"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"atol"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"atoll"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"fgetc"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"fgetln"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"fgets"}}, TR::Prop({{2}}, {{0, ReturnValueIndex}})},
      {{{"fgetws"}}, TR::Prop({{2}}, {{0, ReturnValueIndex}})},
      {{{"fscanf"}}, TR::Prop({{0}}, {{}, 2})},
      {{{"fscanf_s"}}, TR::Prop({{0}}, {{}, {2}})},
      {{{"sscanf"}}, TR::Prop({{0}}, {{}, 2})},

      {{{"getc"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"getc_unlocked"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"getdelim"}}, TR::Prop({{3}}, {{0}})},
      {{{"getline"}}, TR::Prop({{2}}, {{0}})},
      {{{"getw"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"pread"}}, TR::Prop({{0, 1, 2, 3}}, {{1, ReturnValueIndex}})},
      {{{"read"}}, TR::Prop({{0, 2}}, {{1, ReturnValueIndex}})},
      {{{"strchr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strrchr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"tolower"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"toupper"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"fread"}}, TR::Prop({{3}}, {{0, ReturnValueIndex}})},
      {{{"recv"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},
      {{{"recvfrom"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},

      {{{"ttyname"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"ttyname_r"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},

      {{{"basename"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"dirname"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"fnmatch"}}, TR::Prop({{1}}, {{ReturnValueIndex}})},
      {{{"memchr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"memrchr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"rawmemchr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{{"mbtowc"}}, TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{{"wctomb"}}, TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{{"wcwidth"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{{"memcmp"}}, TR::Prop({{0, 1}}, {{ReturnValueIndex}})},
      {{{"memcpy"}}, TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{{"memmove"}}, TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      // If memmem was called with a tainted needle and the search was
      // successful, that would mean that the value pointed by the return value
      // has the same content as the needle. If we choose to go by the policy of
      // content equivalence implies taintedness equivalence, that would mean
      // haystack should be considered a propagation source argument.
      {{{"memmem"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      // The comment for memmem above also applies to strstr.
      {{{"strstr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strcasestr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strtok"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{{"strchrnul"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{{"index"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"rindex"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      // FIXME: In case of arrays, only the first element of the array gets
      // tainted.
      {{{"qsort"}}, TR::Prop({{0}}, {{0}})},
      {{{"qsort_r"}}, TR::Prop({{0}}, {{0}})},

      {{{"strcmp"}}, TR::Prop({{0, 1}}, {{ReturnValueIndex}})},
      {{{"strcasecmp"}}, TR::Prop({{0, 1}}, {{ReturnValueIndex}})},
      {{{"strncmp"}}, TR::Prop({{0, 1, 2}}, {{ReturnValueIndex}})},
      {{{"strncasecmp"}}, TR::Prop({{0, 1, 2}}, {{ReturnValueIndex}})},
      {{{"strspn"}}, TR::Prop({{0, 1}}, {{ReturnValueIndex}})},
      {{{"strcspn"}}, TR::Prop({{0, 1}}, {{ReturnValueIndex}})},
      {{{"strpbrk"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strndup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strndupa"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      // strlen, wcslen, strnlen and alike intentionally don't propagate taint.
      // See the details here: https://github.com/llvm/llvm-project/pull/66086

      {{{"strtol"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},
      {{{"strtoll"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},
      {{{"strtoul"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},
      {{{"strtoull"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},

      {{{"isalnum"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isalpha"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isascii"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isblank"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"iscntrl"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isdigit"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isgraph"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"islower"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isprint"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"ispunct"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isspace"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isupper"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isxdigit"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{{"strdup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strndup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"xstrdup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"memdup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"xmemdup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{CDF_MaybeBuiltin, {BI.getName(Builtin::BIstrncat)}},
       TR::Prop({{1, 2}}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {BI.getName(Builtin::BIstrlcpy)}},
       TR::Prop({{1, 2}}, {{0}})},
      {{CDF_MaybeBuiltin, {BI.getName(Builtin::BIstrlcat)}},
       TR::Prop({{1, 2}}, {{0}})},
      {{CDF_MaybeBuiltin, {{"snprintf"}}},
       TR::Prop({{1}, 3}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"sprintf"}}},
       TR::Prop({{1}, 2}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"strcpy"}}},
       TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"strncpy"}}},
       TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"stpcpy"}}},
       TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"strcat"}}},
       TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"wcsncat"}}},
       TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"strdup"}}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"strdupa"}}},
       TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"wcsdup"}}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
  };

  StaticTaintRules.emplace(std::make_move_iterator(GlobalCRules.begin()),
                           std::make_move_iterator(GlobalCRules.end()));

  // User-provided taint configuration.
  CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
  assert(Mgr);
  CredentialSourceTrackRuleParser ConfigParser{*Mgr};
  std::string Option{"Config"};
  StringRef ConfigFile =
      Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
  std::optional<TaintConfiguration> Config =
      getConfiguration<TaintConfiguration>(*Mgr, this, Option, ConfigFile);
  if (!Config) {
    DynamicTaintRules = RuleLookupTy{};
    return;
  }

  CredentialSourceTrackRuleParser::RulesContTy Rules{
      ConfigParser.parseConfiguration(Option, std::move(*Config))};

  DynamicTaintRules.emplace(std::make_move_iterator(Rules.begin()),
                            std::make_move_iterator(Rules.end()));
}

void CredentialSourceTrackChecker::checkPreCall(const CallEvent &Call,
                                       CheckerContext &C) const {
  if(cs_debug_output_path == ""){
      CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
      assert(Mgr);
      std::string Option{"DOutput"};
      cs_debug_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
      std::ofstream file;
      file.open(cs_debug_output_path,std::ios::out);
      file.close();
  }
  if(cs_other_output_path == ""){
      CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
      assert(Mgr);
      std::string Option{"OOutput"};
      cs_other_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
      std::ofstream file;
      file.open(cs_other_output_path,std::ios::out);
      file.close();
  }

  std::ofstream debugfile;
  debugfile.open(cs_debug_output_path,std::ios::app);

  debugfile << "\n----checkPreCall----\n";
  if (Call.getCalleeIdentifier()){
    debugfile << Call.getCalleeIdentifier()->getName().str() << "\n";
  }

  debugfile << "\n";
  
  std::string debug = "";
  llvm::raw_string_ostream doutput(debug);
  Call.dump(doutput);
  C.getStackFrame()->dumpStack(doutput);
  debugfile << debug << "\n";

  initTaintRules(C);

  // FIXME: this should be much simpler.
  if (const auto *Rule = Call.isGlobalCFunction() ? StaticTaintRules->lookup(Call) : nullptr){
    debugfile << "Global Taint Rule Matched!\n";
    debugfile.close();
    Rule->process(*this, Call, C);
  }
  else if (const auto *Rule = DynamicTaintRules->lookup(Call)){
    debugfile << "Dynamic Taint Rule Matched!\n";
    debugfile.close();
    Rule->process(*this, Call, C);
  }

}

void CredentialSourceTrackChecker::checkPostCall(const CallEvent &Call,
                                        CheckerContext &C) const {
  if(cs_debug_output_path == ""){
      CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
      assert(Mgr);
      std::string Option{"DOutput"};
      cs_debug_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
      std::ofstream file;
      file.open(cs_debug_output_path,std::ios::out);
      file.close();
  }
  if(cs_other_output_path == ""){
      CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
      assert(Mgr);
      std::string Option{"OOutput"};
      cs_other_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
      std::ofstream file;
      file.open(cs_other_output_path,std::ios::out);
      file.close();
  }

  std::ofstream debugfile;
  debugfile.open(cs_debug_output_path,std::ios::app);
  std::string debug_str = "";
  llvm::raw_string_ostream doutput(debug_str);

  debugfile << "\n----checkPostCall----\n";
  if (Call.getCalleeIdentifier()){
    debugfile << Call.getCalleeIdentifier()->getName().str() << "\n";
  }
  
  ProgramStateRef State = C.getState();
  const StackFrameContext *CurrentFrame = C.getStackFrame();
  
  TaintArgsOnPostVisitTy TaintArgsMap = State->get<TaintArgsOnPostVisit>();
  TaintTagsOnPostVisitTy TaintTagsMap = State->get<TaintTagsOnPostVisit>();

  const ImmutableSet<ArgIdxTy> *TaintArgs = TaintArgsMap.lookup(CurrentFrame);
  if (!TaintArgs)
    return;
  assert(!TaintArgs->isEmpty());

  const ImmutableSet<TaintTagType> *TaintTags = TaintTagsMap.lookup(CurrentFrame);
  if (!TaintTags)
    return;
  assert(!TaintTags->isEmpty());

  auto &F = State->getStateManager().get_context<ArgIdxFactory>();
  auto &FF = State->getStateManager().get_context<TaintTagSet>();

  ImmutableSet<ArgIdxTy> GetTaintArgs = F.getEmptySet();
  ImmutableSet<TaintTagType> GetTaintTags = FF.getEmptySet();
  
  for(ImmutableSet<ArgIdxTy>::iterator TI = TaintArgs->begin(), TE = TaintArgs->end(); TI != TE; ++TI){
    debugfile << *TI << " ";
    GetTaintArgs = F.add(GetTaintArgs, *TI);
  }
  for(ImmutableSet<TaintTagType>::iterator TI = TaintTags->begin(), TE = TaintTags->end(); TI != TE; ++TI){
    debugfile << *TI << " ";
    GetTaintTags = FF.add(GetTaintTags, *TI);
  }
  
  debug_str = "";
  doutput << "PostCall<";
  Call.dump(doutput);
  doutput << "> actually wants to taint arg index: ";
  for (ArgIdxTy I : *TaintArgs) {
    
    doutput << I << ' ';
  }
  doutput << "; tags: ";
  for (TaintTagType I : *TaintTags) {
    
    doutput << I << ' ';
  }
  debugfile << debug_str;

  for (ArgIdxTy ArgNum : *TaintArgs) {
    // Special handling for the tainted return value.
    if (ArgNum == ReturnValueIndex) {
      for (TaintTagType tag : *TaintTags){
        State = addTaint(State, Call.getReturnValue(), tag);
      }
      continue;
    }
    
    if (auto V = getPointeeOf(State, Call.getArgSVal(ArgNum))) {
      debugfile << "This is Pointer\n";
      for (TaintTagType tag : *TaintTags){
        State = addTaint(State, *V, tag);
        SymbolRef Sym = ((SVal)*V).getAsSymbol(true);
        if (Sym){
            debugfile << "get Symbol\n";
            // for (SymExpr::symbol_iterator SI = Sym->symbol_begin(), SE = Sym->symbol_end(); SI != SE; ++SI) {
            for (SymbolRef SubSym : Sym->symbols()){
                if (!isa<SymbolData>(SubSym))
                    continue;

                if (const auto *SD = dyn_cast<SymbolDerived>(SubSym)) {
                    // If this is a SymbolDerived with a tainted parent, it's also tainted.
                    debugfile << "This is SymbolDerived\n";
                    State = addTaint(State, SD->getParentSymbol(), tag);
                    State = addTaint(State, SD->getOriginRegion(), tag);
                }
            }
        }
      }
    }else{
      debugfile << "This is not Pointer\n";
      for (TaintTagType tag : *TaintTags){
        State = addTaint(State, Call.getArgSVal(ArgNum), tag);
      }
    }
  }

  State = State->remove<TaintArgsOnPostVisit>(CurrentFrame);
  State = State->remove<TaintTagsOnPostVisit>(CurrentFrame);
  C.addTransition(State);
}


// password = optarg
void CredentialSourceTrackChecker::checkPreStmt(const BinaryOperator *BO,
                                        CheckerContext &C) const {
  
  if(cs_debug_output_path == ""){
      CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
      assert(Mgr);
      std::string Option{"DOutput"};
      cs_debug_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
      std::ofstream file;
      file.open(cs_debug_output_path,std::ios::out);
      file.close();
  }
  if(cs_other_output_path == ""){
      CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
      assert(Mgr);
      std::string Option{"OOutput"};
      cs_other_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
      std::ofstream file;
      file.open(cs_other_output_path,std::ios::out);
      file.close();
  }


  ProgramStateRef State = C.getState();
  const StackFrameContext *CurrentFrame = C.getStackFrame();
  BinaryOperatorKind OK = BO->getOpcode();
  if (!BO->isAssignmentOp()){
    return;
  }

  std::ofstream debugfile;
  debugfile.open(cs_debug_output_path,std::ios::app);

  debugfile << "\n----checkPreStmt: BinaryOperator ----\n\n";
  std::string debug_str = "";
  llvm::raw_string_ostream doutput(debug_str);
  BO->dump(doutput, C.getASTContext());
  debugfile << debug_str << "\n";


  TaintTagType tagvalue = 0;
  SVal RVal = State->getSVal(BO->getRHS(), C.getLocationContext());
  SVal LVal = State->getSVal(BO->getLHS(), C.getLocationContext());
  debugfile << "\n++++++++++++++++ LVal\n";
  debug_str = "";
  LVal.dumpToStream(doutput);
  debugfile << debug_str << "\n";
  debugfile << "\n++++++++++++++++ RVal\n";
  debug_str = "";
  RVal.dumpToStream(doutput);
  debugfile << debug_str << "\n";

  bool IsOptarg = isOptargVar(BO->getRHS());
  if(IsOptarg){
    debugfile << "Right value is optarg \n";
    if (auto V = getPointeeOf(State, C.getSVal(BO->getRHS()))){
      State = addTaint(State, *V, TaintTagCredSrcOptarg);
      SymbolRef Sym = ((SVal)*V).getAsSymbol(true);
      if (Sym){
        // for (SymExpr::symbol_iterator SI = Sym->symbol_begin(), SE = Sym->symbol_end(); SI != SE; ++SI) {
        for (SymbolRef SubSym : Sym->symbols()){
          if (!isa<SymbolData>(SubSym))
            continue;

          if (const auto *SD = dyn_cast<SymbolDerived>(SubSym)) {
            // If this is a SymbolDerived with a tainted parent, it's also tainted.
            State = addTaint(State, SD->getParentSymbol(), TaintTagCredSrcOptarg);
            State = addTaint(State, SD->getOriginRegion(), TaintTagCredSrcOptarg);
          }
        }
      }
    }else{
      State = addTaint(State, C.getSVal(BO->getRHS()), TaintTagCredSrcOptarg);
    }
  }

  bool IsStdin = isStdinVar(BO->getRHS());
  if(IsStdin){
    debugfile << "Right value is stdin \n";
    if (auto V = getPointeeOf(State, C.getSVal(BO->getRHS()))){
      State = addTaint(State, *V, TaintTagCredSrcOtherInput);
      SymbolRef Sym = ((SVal)*V).getAsSymbol(true);
      if (Sym){
        // for (SymExpr::symbol_iterator SI = Sym->symbol_begin(), SE = Sym->symbol_end(); SI != SE; ++SI) {
        for (SymbolRef SubSym : Sym->symbols()) {
          if (!isa<SymbolData>(SubSym))
            continue;

          if (const auto *SD = dyn_cast<SymbolDerived>(SubSym)) {
            // If this is a SymbolDerived with a tainted parent, it's also tainted.
            State = addTaint(State, SD->getParentSymbol(), TaintTagCredSrcOtherInput);
            State = addTaint(State, SD->getOriginRegion(), TaintTagCredSrcOtherInput);
          }
        }
      }
    }else{
      State = addTaint(State, C.getSVal(BO->getRHS()), TaintTagCredSrcOtherInput);
    }
  }

  debugfile.close();

  // Clear up the taint info from the state.
//   State = State->remove<TaintArgsOnPostVisit>(CurrentFrame);
  C.addTransition(State);

}


// password = getenv("xxx")
// password = optarg
// password = open(xxx)
void CredentialSourceTrackChecker::checkPostStmt(const BinaryOperator *BO,
                                        CheckerContext &C) const {
  
  if(cs_debug_output_path == ""){
      CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
      assert(Mgr);
      std::string Option{"DOutput"};
      cs_debug_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
      std::ofstream file;
      file.open(cs_debug_output_path,std::ios::out);
      file.close();
  }
  if(cs_other_output_path == ""){
      CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
      assert(Mgr);
      std::string Option{"OOutput"};
      cs_other_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
      std::ofstream file;
      file.open(cs_other_output_path,std::ios::out);
      file.close();
  }


  ProgramStateRef State = C.getState();
  const StackFrameContext *CurrentFrame = C.getStackFrame();
  BinaryOperatorKind OK = BO->getOpcode();
  if (!BO->isAssignmentOp()){
    return;
  }

  std::ofstream debugfile;
  debugfile.open(cs_debug_output_path,std::ios::app);

  debugfile << "\n----checkPostStmt: BinaryOperator ----\n\n";
  std::string debug_str = "";
  llvm::raw_string_ostream doutput(debug_str);
  BO->dump(doutput, C.getASTContext());
  debugfile << debug_str << "\n";


  TaintTagType tagvalue = 0;
  SVal RVal = State->getSVal(BO->getRHS(), C.getLocationContext());
  SVal LVal = State->getSVal(BO->getLHS(), C.getLocationContext());
  debugfile << "\n++++++++++++++++ LVal\n";
  debug_str = "";
  LVal.dumpToStream(doutput);
  debugfile << debug_str << "\n";
  debugfile << "\n++++++++++++++++ RVal\n";
  debug_str = "";
  RVal.dumpToStream(doutput);
  debugfile << debug_str << "\n";

  bool IsCred = isCredentialVar(BO->getLHS());
  if(!IsCred){
    return;
  }

  debugfile << "\nLeft is Credential Variable\n";
  debugfile.close();

  isVulnerableVar(BO->getRHS(), State, C);

}

void CredentialSourceTrackChecker::printState(raw_ostream &Out, ProgramStateRef State,
                                     const char *NL, const char *Sep) const {
  printTaint(State, Out, NL, Sep);
}

void CredentialSourceTrackRule::process(const CredentialSourceTrackChecker &Checker,
                               const CallEvent &Call, CheckerContext &C) const {
  std::ofstream debugfile;
  debugfile.open(cs_debug_output_path,std::ios::app);

  ProgramStateRef State = C.getState();
  const ArgIdxTy CallNumArgs = fromArgumentCount(Call.getNumArgs());
  
  const auto ForEachCallArg = [&C, &Call, CallNumArgs](auto &&Fun) {
    for (ArgIdxTy I = ReturnValueIndex; I < CallNumArgs; ++I) {
      const Expr *E = GetArgExpr(I, Call);
      Fun(I, E, C.getSVal(E));
    }
  };

  bool IsTaintedSrcFile = false;
  bool IsTaintedSrcEnv = false;
  bool IsTaintedSrcConst = false;
  bool IsTaintedSrcOptarg = false;
  bool IsTaintedSrcOther = false;
  bool IsCred = false;
  

  ForEachCallArg([this, &Checker, &C, &State, &IsTaintedSrcFile, &IsTaintedSrcEnv, &IsTaintedSrcConst, &IsTaintedSrcOptarg, &IsTaintedSrcOther, &IsCred, &debugfile](ArgIdxTy I, const Expr *E, SVal) {
    IsTaintedSrcFile = IsTaintedSrcFile || (PropSrcArgs.contains(I) && isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcFile));
    IsTaintedSrcEnv = IsTaintedSrcEnv || (PropSrcArgs.contains(I) && isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcEnv));
    IsTaintedSrcConst = IsTaintedSrcConst || (PropSrcArgs.contains(I) && isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcConst));
    IsTaintedSrcOptarg = IsTaintedSrcOptarg || (PropSrcArgs.contains(I) && (isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcOptarg) || isOptargVar(E)));
    IsTaintedSrcOther = IsTaintedSrcOther || (PropSrcArgs.contains(I) && isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcOtherInput));
    IsCred = IsCred || (PropDstArgs.contains(I) && isCredentialVar(E)) || (SourceArgs.contains(I) && isCredentialVar(E));

    if(IsCred){
      debugfile << "\nFind password variable.\n";
    }
    
    if(IsTaintedSrcFile && IsCred){
        debugfile << "\nFind set up tainted data from external file to password (via propagation)!!!!\n";
        Checker.generateReportIfTainted(E, MsgCustomSinkFile, C);
    }
    else if(IsTaintedSrcEnv && IsCred){
        debugfile << "\nFind set up tainted data from environment to password (via propagation)!!!!\n";
        Checker.generateReportIfTainted(E, MsgCustomSinkEnv, C);
    }
    else if(IsTaintedSrcOptarg && IsCred){
        debugfile << "\nFind set up tainted data from Optarg to password (via propagation)!!!!\n";
        Checker.generateReportIfTainted(E, MsgCustomSinkArg, C);
    }
    else if(IsTaintedSrcConst && IsCred){
        debugfile << "\nFind set up tainted data from Constant to password (via propagation)!!!!\n";
        Checker.generateReportIfTainted(E, MsgCustomSinkConst, C);
    }
    else if(IsTaintedSrcOther && IsCred){
        debugfile << "\nFind set up tainted data from other input to password (via propagation)!!!!\n";
        Checker.generateReportIfTainted(E, MsgCustomSinkOther, C);
    }
  });


  ForEachCallArg([this, &State](ArgIdxTy I, const Expr *E, SVal S) {
    if (FilterArgs.contains(I)) {
      State = removeTaint(State, S);
      if (auto P = getPointeeOf(State, S))
        State = removeTaint(State, *P);
    }
  });
  debugfile << "\nIsTaintedSrcFile = " << IsTaintedSrcFile << "; IsTaintedSrcEnv = " << IsTaintedSrcEnv << "; IsTaintedSrcConst = " << IsTaintedSrcConst << "; IsTaintedSrcOptarg = " << IsTaintedSrcOptarg << "; IsTaintedSrcOther = " << IsTaintedSrcOther << "\n";
  

  bool IsMatching = PropSrcArgs.isEmpty();
  ForEachCallArg(
      [this, &C, &IsMatching, &State, &debugfile](ArgIdxTy I, const Expr *E, SVal) {
        IsMatching = IsMatching || (PropSrcArgs.contains(I) &&
                                    (isTaintedOrPointsToTainted(State, C.getSVal(E)) || isFileVar(E) || isConstVar(E) || isOptargVar(E) || isCredentialVar(E)));
        debugfile << "For taint propagation: Indx = " << I << ", PropSrcArgs = " << PropSrcArgs.contains(I) << ", IsTainted = " << (isTaintedOrPointsToTainted(State, C.getSVal(E))) << "\n";
  });

  debugfile << "\nIsMatching = " << IsMatching << "\n";
  
  if (!IsMatching)
    return;

  const auto WouldEscape = [](SVal V, QualType Ty) -> bool {
    if (!isa<Loc>(V))
      return false;

    const bool IsNonConstRef = Ty->isReferenceType() && !Ty.isConstQualified();
    const bool IsNonConstPtr =
        Ty->isPointerType() && !Ty->getPointeeType().isConstQualified();

    return IsNonConstRef || IsNonConstPtr;
  };

  /// Propagate taint where it is necessary.
  auto &F = State->getStateManager().get_context<ArgIdxFactory>();
  auto &FF = State->getStateManager().get_context<TaintTagSet>();
  ImmutableSet<ArgIdxTy> TaintArgs = F.getEmptySet();
  ImmutableSet<TaintTagType> TaintTags = FF.getEmptySet();

  IsTaintedSrcFile = false;
  IsTaintedSrcEnv = false;
  IsTaintedSrcConst = false;
  IsTaintedSrcOptarg = false;
  IsTaintedSrcOther = false;
  IsCred = false;
  ForEachCallArg([&](ArgIdxTy I, const Expr *E, SVal) {
    IsTaintedSrcFile = IsTaintedSrcFile || (PropSrcArgs.contains(I) && (isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcFile) || isFileVar(E))) || (SourceArgs.contains(I) && SrcMsg == TaintTagCredSrcFile);
    IsTaintedSrcEnv = IsTaintedSrcEnv || (PropSrcArgs.contains(I) && isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcEnv)) || (SourceArgs.contains(I) && SrcMsg == TaintTagCredSrcEnv);
    IsTaintedSrcConst = IsTaintedSrcConst || (PropSrcArgs.contains(I) && (isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcConst) || isConstVar(E))) || (SourceArgs.contains(I) && SrcMsg == TaintTagCredSrcConst);
    IsTaintedSrcOptarg = IsTaintedSrcOptarg || (PropSrcArgs.contains(I) && (isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcOptarg) || isOptargVar(E))) || (SourceArgs.contains(I) && SrcMsg == TaintTagCredSrcOptarg);
    IsTaintedSrcOther = IsTaintedSrcOther || (PropSrcArgs.contains(I) && isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcOtherInput)) || (SourceArgs.contains(I) && SrcMsg == TaintTagCredSrcOtherInput);
    IsCred = IsCred || (PropSrcArgs.contains(I) && isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCred)) || isCredentialVar(E);
  });

  debugfile << "\nIsTaintedSrcFile = " << IsTaintedSrcFile << "; IsTaintedSrcEnv = " << IsTaintedSrcEnv << "; IsTaintedSrcConst = " << IsTaintedSrcConst << "; IsTaintedSrcOptarg = " << IsTaintedSrcOptarg << "; IsTaintedSrcOther = " << IsTaintedSrcOther << "; IsCred = " << IsCred << "\n";

  if (IsTaintedSrcFile){
    TaintTags = FF.add(TaintTags, TaintTagCredSrcFile);
  }
  if (IsTaintedSrcEnv){
    TaintTags = FF.add(TaintTags, TaintTagCredSrcEnv);
  }
  if (IsTaintedSrcConst){
    TaintTags = FF.add(TaintTags, TaintTagCredSrcConst);
  }
  if (IsTaintedSrcOptarg){
    TaintTags = FF.add(TaintTags, TaintTagCredSrcOptarg);
  }
  if (IsTaintedSrcOther){
    TaintTags = FF.add(TaintTags, TaintTagCredSrcOtherInput);
  }
  if (IsCred){
    TaintTags = FF.add(TaintTags, TaintTagCred);
  }

  ForEachCallArg(
      [&](ArgIdxTy I, const Expr *E, SVal V) {
        if(SourceArgs.contains(I)){
          debugfile << "\nPreCall SourceArgs<";
          std::string debug = "";
          llvm::raw_string_ostream doutput(debug);
          Call.dump(doutput);
          debugfile << debug;
          debugfile << "> prepares tainting arg index: " << I << '\n';
          TaintArgs = F.add(TaintArgs, I);
        }
        if (PropDstArgs.contains(I)) {
          debugfile << "\nPreCall PropDstArgs<";
          std::string debug = "";
          llvm::raw_string_ostream doutput(debug);
          Call.dump(doutput);
          debugfile << debug;
          debugfile << "> prepares tainting arg index: " << I << '\n';

          TaintArgs = F.add(TaintArgs, I);
        }

        // Taint property gets lost if the variable is passed as a
        // non-const pointer or reference to a function which is
        // not inlined. For matching rules we want to preserve the taintedness.
        // TODO: We should traverse all reachable memory regions via the
        // escaping parameter. Instead of doing that we simply mark only the
        // referred memory region as tainted.
        if (WouldEscape(V, E->getType())) {
          debugfile << "\nPreCall<";
          std::string debug = "";
          llvm::raw_string_ostream doutput(debug);
          Call.dump(doutput);
          debugfile << debug << "\n";
          debugfile << "> prepares tainting arg index: " << I << '\n';

          TaintArgs = F.add(TaintArgs, I);
        }
      });

  if (!TaintArgs.isEmpty())
    State = State->set<TaintArgsOnPostVisit>(C.getStackFrame(), TaintArgs);
  if (!TaintTags.isEmpty())
    State = State->set<TaintTagsOnPostVisit>(C.getStackFrame(), TaintTags);
  C.addTransition(State);
}

bool CredentialSourceTrackChecker::generateReportIfTainted(const Expr *E, StringRef Msg,
                                                  CheckerContext &C) const {
  assert(E);
  std::optional<SVal> TaintedSVal =
      getPointeeOrPointer(C.getState(), C.getSVal(E));

  if (!TaintedSVal)
    return false;

  // Generate diagnostic.
  if (ExplodedNode *N = C.generateNonFatalErrorNode()) {
    auto report = std::make_unique<PathSensitiveBugReport>(BT, Msg, N);
    report->addRange(E->getSourceRange());
    report->addVisitor(std::make_unique<TaintBugVisitor>(*TaintedSVal));

    C.emitReport(std::move(report));
    return true;
  }
  return false;
}


void CredentialSourceTrackChecker::isVulnerableVar(const Expr *E, const ProgramStateRef &State, CheckerContext &C) const {
  std::ofstream debugfile;
  debugfile.open(cs_debug_output_path,std::ios::app);

  debugfile << "\n---isVulnerableVar---\n";
  // llvm::dbgs() << "\n---isVulnerableVar---\n";

  SVal RVal = State->getSVal(E, C.getLocationContext());

  bool IsTaintedEnvSrc = isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcEnv);
  if(IsTaintedEnvSrc){
    debugfile << "\nFind set up env data to password!!!!\n";
    debugfile.close();
    generateReportIfTainted(E, MsgCustomSinkEnv, C);
    // return MsgCustomSinkEnv;
  }

  bool IsTaintedFileSrc = isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcFile);
  if(IsTaintedFileSrc){
    debugfile << "\nFind set up file data to password!!!!\n";
    debugfile.close();
    generateReportIfTainted(E, MsgCustomSinkFile, C);
    // return MsgCustomSinkFile;
  }

  bool IsOptarg = isOptargVar(E) || isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcOptarg);
  if(IsOptarg){
      debugfile << "\nFind set up optarg data to password!!!\n";
      debugfile.close();
      generateReportIfTainted(E, MsgCustomSinkArg, C);
      // return MsgCustomSinkArg;
  }

  bool IsConstSrc = isConstVar(E);
  if(IsConstSrc){
    debugfile << "\nFind set up constant data to password!!!!\n";
    debugfile.close();
    generateReportIfTainted(E, MsgCustomSinkConst, C);
    // return MsgCustomSinkConst;
  }

  bool IsTaintedOther = isStdinVar(E) || isTaintedOrPointsToTainted(State, C.getSVal(E), TaintTagCredSrcOtherInput);
  if(IsTaintedOther){
    debugfile << "\nFind set up other external data to password!!!!\n";
    debugfile.close();
    generateReportIfTainted(E, MsgCustomSinkOther, C);
    // return MsgCustomSinkFile;
  }

  
  debugfile.close();
}


// /// TODO: remove checking for printf format attributes and socket whitelisting
// /// from GenericTaintChecker, and that means the following functions:
// /// getPrintfFormatArgumentNum,
// /// GenericTaintChecker::checkUncontrolledFormatString,
// /// GenericTaintChecker::taintUnsafeSocketProtocol

// static bool getPrintfFormatArgumentNum(const CallEvent &Call,
//                                        const CheckerContext &C,
//                                        ArgIdxTy &ArgNum) {
//   // Find if the function contains a format string argument.
//   // Handles: fprintf, printf, sprintf, snprintf, vfprintf, vprintf, vsprintf,
//   // vsnprintf, syslog, custom annotated functions.
//   const Decl *CallDecl = Call.getDecl();
//   if (!CallDecl)
//     return false;
//   const FunctionDecl *FDecl = CallDecl->getAsFunction();
//   if (!FDecl)
//     return false;

//   const ArgIdxTy CallNumArgs = fromArgumentCount(Call.getNumArgs());

//   for (const auto *Format : FDecl->specific_attrs<FormatAttr>()) {
//     ArgNum = Format->getFormatIdx() - 1;
//     if ((Format->getType()->getName() == "printf") && CallNumArgs > ArgNum)
//       return true;
//   }

//   return false;
// }

// bool GenericTaintChecker::checkUncontrolledFormatString(
//     const CallEvent &Call, CheckerContext &C) const {
//   // Check if the function contains a format string argument.
//   ArgIdxTy ArgNum = 0;
//   if (!getPrintfFormatArgumentNum(Call, C, ArgNum))
//     return false;

//   // If either the format string content or the pointer itself are tainted,
//   // warn.
//   return generateReportIfTainted(Call.getArgExpr(ArgNum),
//                                  MsgUncontrolledFormatString, C);
// }

// void GenericTaintChecker::taintUnsafeSocketProtocol(const CallEvent &Call,
//                                                     CheckerContext &C) const {
//   if (Call.getNumArgs() < 1)
//     return;
//   const IdentifierInfo *ID = Call.getCalleeIdentifier();
//   if (!ID)
//     return;
//   if (!ID->getName().equals("socket"))
//     return;

//   SourceLocation DomLoc = Call.getArgExpr(0)->getExprLoc();
//   StringRef DomName = C.getMacroNameOrSpelling(DomLoc);
//   // Allow internal communication protocols.
//   bool SafeProtocol = DomName.equals("AF_SYSTEM") ||
//                       DomName.equals("AF_LOCAL") || DomName.equals("AF_UNIX") ||
//                       DomName.equals("AF_RESERVED_36");
//   if (SafeProtocol)
//     return;

//   ProgramStateRef State = C.getState();
//   auto &F = State->getStateManager().get_context<ArgIdxFactory>();
//   ImmutableSet<ArgIdxTy> Result = F.add(F.getEmptySet(), ReturnValueIndex);
//   State = State->set<TaintArgsOnPostVisit>(C.getStackFrame(), Result);
//   C.addTransition(State);
// }

/// Checker registration
void ento::registerCredentialSourceTrackChecker(CheckerManager &Mgr) {
  Mgr.registerChecker<CredentialSourceTrackChecker>();
}

bool ento::shouldRegisterCredentialSourceTrackChecker(const CheckerManager &mgr) {
  return true;
}
