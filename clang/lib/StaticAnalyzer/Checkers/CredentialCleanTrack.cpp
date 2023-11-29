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
#include <utility>

#include<sstream>
#include<iostream>
#include<fstream>
#include<string.h>
#include<map>

using namespace std;

#define DEBUG_TYPE "taint-checker"

using namespace clang;
using namespace ento;
using namespace taint;
using namespace llvm;

using llvm::ImmutableSet;

std::string cc_doutput_path = "";
std::string cc_other_output_path = "";

namespace {

class CredentialCleanTrackChecker;

constexpr llvm::StringLiteral MsgCustomSinkNotFree =
    "Credential data is not freed";

constexpr llvm::StringLiteral MsgCustomSinkNotMemset =
    "Credential data is not cleaned";
  
constexpr llvm::StringLiteral MsgCustomSinkNotMemsetFree =
    "Credential data is neither freed or cleaned";


using ArgIdxTy = int;
using ArgVecTy = llvm::SmallVector<ArgIdxTy, 2>;
using TaintTagSet = llvm::ImmutableSet<TaintTagType>;

/// Denotes the return value.
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


std::string str2lower(std::string s){
  for (auto& x : s) {
    x = tolower(x);
  }
  return s;

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


/// ArgSet is used to describe arguments relevant for taint detection or
/// taint application. A discrete set of argument indexes and a variadic
/// argument list signified by a starting index are supported.
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

class CredentialCleanTrackRule {
  ArgSet SinkArgs;
  ArgSet SourceArgs;
  ArgSet FilterArgs;
  ArgSet PropSrcArgs;
  ArgSet PropDstArgs;


  std::optional<TaintTagType> SrcMsg;
  std::optional<StringRef> SinkMsg;

  CredentialCleanTrackRule() = default;

  CredentialCleanTrackRule(ArgSet &&Sink, ArgSet &&Source, ArgSet &&Filter, ArgSet &&Src, ArgSet &&Dst, 
                   std::optional<TaintTagType> SrcMsg = TaintTagNone,
                   std::optional<StringRef> SinkMsg = std::nullopt)
      : SinkArgs(std::move(Sink)), SourceArgs(std::move(Source)), 
        FilterArgs(std::move(Filter)),
        PropSrcArgs(std::move(Src)), PropDstArgs(std::move(Dst)), 
        SrcMsg(SrcMsg), SinkMsg(SinkMsg) {}

public:
  static CredentialCleanTrackRule Sink(ArgSet &&SinkArgs, std::optional<StringRef> Msg = std::nullopt) {
    return {std::move(SinkArgs), {}, {}, {}, {}, TaintTagNone, Msg};
  }

  static CredentialCleanTrackRule Filter(ArgSet &&FilterArgs) {
    return {{}, {}, std::move(FilterArgs), {}, {}};
  }

  static CredentialCleanTrackRule Source(ArgSet &&SourceArgs, std::optional<TaintTagType> Msg = TaintTagNone) {
    return {{}, std::move(SourceArgs), {}, {}, {}, Msg, std::nullopt};
  }

  static CredentialCleanTrackRule Prop(ArgSet &&SrcArgs, ArgSet &&DstArgs) {
    return {{}, {}, {}, std::move(SrcArgs), std::move(DstArgs)};
  }

  static CredentialCleanTrackRule SinkProp(ArgSet &&SinkArgs, ArgSet &&SrcArgs,
                                   ArgSet &&DstArgs,
                                   std::optional<StringRef> Msg = std::nullopt) {
    return {
        std::move(SinkArgs), {}, {}, std::move(SrcArgs), std::move(DstArgs), TaintTagNone, Msg};
  }

  void process(const CredentialCleanTrackChecker &Checker, const CallEvent &Call,
               CheckerContext &C, raw_ostream &debugfile) const;

  static const Expr *GetArgExpr(ArgIdxTy ArgIdx, const CallEvent &Call) {
    return ArgIdx == ReturnValueIndex ? Call.getOriginExpr()
                                      : Call.getArgExpr(ArgIdx);
  };

  static bool UntrustedEnv(CheckerContext &C);
};

using RuleLookupTy = CallDescriptionMap<CredentialCleanTrackRule>;


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

struct CredentialCleanTrackRuleParser {
  CredentialCleanTrackRuleParser(CheckerManager &Mgr) : Mgr(Mgr) {}
  using RulesContTy = std::vector<std::pair<CallDescription, CredentialCleanTrackRule>>;
  RulesContTy parseConfiguration(const std::string &Option,
                                 TaintConfiguration &&Config) const;

private:
  using NamePartsTy = llvm::SmallVector<StringRef, 2>;

  void validateArgVector(const std::string &Option, const ArgVecTy &Args) const;

  template <typename Config> static NamePartsTy parseNameParts(const Config &C);

  template <typename Config>
  static void consumeRulesFromConfig(const Config &C, CredentialCleanTrackRule &&Rule,
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

class CredentialCleanTrackChecker : public Checker<check::PreCall, check::PostCall, 
                                                    check::PostStmt<DeclStmt>,
                                                    check::PreStmt<BinaryOperator>,
                                                    check::PostStmt<BinaryOperator>,
                                                    check::DeadSymbols
                                                    > {
public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostStmt(const DeclStmt *DS, CheckerContext &C) const;
  void checkPreStmt(const BinaryOperator *BO, CheckerContext &C) const;
  void checkPostStmt(const BinaryOperator *BO, CheckerContext &C) const;
  void checkDeadSymbols(SymbolReaper & SymReaper , CheckerContext &C) const;

  void printState(raw_ostream &Out, ProgramStateRef State, const char *NL,
                  const char *Sep) const override;

  /// Generate a report if the expression is tainted or points to tainted data.
  bool generateReportIfTainted(const Expr *E, StringRef Msg,
                               CheckerContext &C) const;

  bool generateReportIfTainted1(SymbolRef Sym, const ElementRegion *ER, StringRef Msg,
                               CheckerContext &C) const;
  
  bool isTaintedOrPointsToTainted1(SVal S, const ProgramStateRef &State,
                                CheckerContext &C, TaintTagType tag = TaintTagNone) const;

  ProgramStateRef addTaintedCallExprRet(ProgramStateRef &State, SVal S, CheckerContext &C) const;
  
  void printCredTaints(raw_ostream &Out, ProgramStateRef State) const;

  ProgramStateRef addCredVar(ProgramStateRef State, SVal V, TaintTagType Kind) const;
  ProgramStateRef addCredVar(ProgramStateRef State, SymbolRef Sym, TaintTagType Kind) const;
  ProgramStateRef addCredVar(ProgramStateRef State, const MemRegion *R, TaintTagType Kind) const;
  ProgramStateRef addPartialCredVar(ProgramStateRef State, SymbolRef ParentSym, const SubRegion *SubRegion, TaintTagType Kind) const;

  ProgramStateRef removeCredVar(ProgramStateRef State, SVal V) const;
  ProgramStateRef removeCredVar(ProgramStateRef State, SymbolRef Sym) const;
  ProgramStateRef removeCredVar(ProgramStateRef State, const MemRegion *R) const;

  bool checkCredVar(ProgramStateRef State, SVal V, TaintTagType Kind) const;
  bool checkCredVar(ProgramStateRef State, SymbolRef Sym, TaintTagType Kind) const;
  bool checkCredVar(ProgramStateRef State, const MemRegion *R, TaintTagType Kind) const;
  

private:
  const BugType BT{this, "Use of Untrusted Data", "Untrusted Data"};
  
  void initTaintRules(CheckerContext &C) const;

  mutable std::optional<RuleLookupTy> StaticTaintRules;
  mutable std::optional<RuleLookupTy> DynamicTaintRules;
  // mutable 
};
} // end of anonymous namespace

namespace {
  class CredCleanBugVisitor
      : public BugReporterVisitor {
    
    protected:
        SymbolRef Sym;
		const ElementRegion* ER;
		int type; //0 for SymbolRef; 1 for ElementRegion;
    
  public:
    explicit CredCleanBugVisitor(SymbolRef S, const ElementRegion* ER, int type):Sym(S),ER(ER),type(type) {}

    static void *getTag() {
        static int Tag = 0;
        return &Tag;
    }
    void Profile(llvm::FoldingSetNodeID &ID) const override {
        ID.AddPointer(getTag());
        //ID.AddPointer(&Sym);
    }
    
    PathDiagnosticPieceRef VisitNode(const ExplodedNode *N,BugReporterContext &BRC,
                                    PathSensitiveBugReport &BR) override{
            ProgramStateRef state = N->getState();
            ProgramStateRef statePrev = N->getFirstPred()->getState();

            const Stmt *S = N->getStmtForDiagnostics();
            if(!S)
                return nullptr;

            const LocationContext *NCtx = N->getLocationContext();
            PathDiagnosticLocation L =
                PathDiagnosticLocation::createBegin(S, BRC.getSourceManager(), NCtx);
            if (!L.isValid() || !L.asLocation().isValid())
                return nullptr;

            return std::make_shared<PathDiagnosticEventPiece>(L, "Taint originated here");

        }

  private:

  };
} // end anonymous namespace


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
REGISTER_MAP_WITH_PROGRAMSTATE(TaintTagsOnPostVisit, const LocationContext *,
                               ImmutableSet<TaintTagType>)


REGISTER_MAP_FACTORY_WITH_PROGRAMSTATE(TaintedSubRegions, const SubRegion *, TaintTagSet)

REGISTER_MAP_WITH_PROGRAMSTATE(CredSymbolMap, SymbolRef, TaintTagSet)
REGISTER_MAP_WITH_PROGRAMSTATE(CredDerivedSymbolMap, SymbolRef, TaintedSubRegions)
REGISTER_MAP_WITH_PROGRAMSTATE(CredRegionMap, const ElementRegion *, TaintTagSet)
REGISTER_MAP_WITH_PROGRAMSTATE(ReportedSymbol, SymbolRef, int)
REGISTER_MAP_WITH_PROGRAMSTATE(ReportedRegion, const ElementRegion *, int)

REGISTER_SET_FACTORY_WITH_PROGRAMSTATE(ArgIdxFactory, ArgIdxTy)
REGISTER_SET_FACTORY_WITH_PROGRAMSTATE(TaintTagSet, TaintTagType)

// REGISTER_SET_FACTORY_WITH_PROGRAMSTATE(TaintTagSet, TaintTagType)

void CredentialCleanTrackRuleParser::validateArgVector(const std::string &Option,
                                               const ArgVecTy &Args) const {
  for (ArgIdxTy Arg : Args) {
    if (Arg < ReturnValueIndex) {
      Mgr.reportInvalidCheckerOptionValue(
          Mgr.getChecker<CredentialCleanTrackChecker>(), Option,
          "an argument number for propagation rules greater or equal to -1");
    }
  }
}

template <typename Config>
CredentialCleanTrackRuleParser::NamePartsTy
CredentialCleanTrackRuleParser::parseNameParts(const Config &C) {
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
void CredentialCleanTrackRuleParser::consumeRulesFromConfig(const Config &C,
                                                    CredentialCleanTrackRule &&Rule,
                                                    RulesContTy &Rules) {
  NamePartsTy NameParts = parseNameParts(C);
  Rules.emplace_back(CallDescription(NameParts), std::move(Rule));
}

void CredentialCleanTrackRuleParser::parseConfig(const std::string &Option,
                                         TaintConfiguration::Sink &&S,
                                         RulesContTy &Rules) const {
  validateArgVector(Option, S.SinkArgs);
  consumeRulesFromConfig(S, CredentialCleanTrackRule::Sink(std::move(S.SinkArgs)),
                         Rules);
}

void CredentialCleanTrackRuleParser::parseConfig(const std::string &Option,
                                         TaintConfiguration::Source &&S,
                                         RulesContTy &Rules) const {
  validateArgVector(Option, S.SourceArgs);
  consumeRulesFromConfig(S, CredentialCleanTrackRule::Source(std::move(S.SourceArgs), std::move(S.Type)),
                         Rules);
}

void CredentialCleanTrackRuleParser::parseConfig(const std::string &Option,
                                         TaintConfiguration::Filter &&S,
                                         RulesContTy &Rules) const {
  validateArgVector(Option, S.FilterArgs);
  consumeRulesFromConfig(S, CredentialCleanTrackRule::Filter(std::move(S.FilterArgs)),
                         Rules);
}

void CredentialCleanTrackRuleParser::parseConfig(const std::string &Option,
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
      P, CredentialCleanTrackRule::Prop(std::move(SrcDesc), std::move(DstDesc)), Rules);
}

CredentialCleanTrackRuleParser::RulesContTy
CredentialCleanTrackRuleParser::parseConfiguration(const std::string &Option,
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

void CredentialCleanTrackChecker::initTaintRules(CheckerContext &C) const {
  if (StaticTaintRules || DynamicTaintRules)
    return;

  using RulesConstructionTy =
      std::vector<std::pair<CallDescription, CredentialCleanTrackRule>>;
  using TR = CredentialCleanTrackRule;

  const Builtin::Context &BI = C.getASTContext().BuiltinInfo;

  RulesConstructionTy GlobalCRules{
      // Sources
      {{{"memset"}}, TR::Source({{0, ReturnValueIndex}}, TaintTagCredMemset)},
      {{{"memset_s"}}, TR::Source({{0, ReturnValueIndex}}, TaintTagCredMemset)},


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

      {{{"strdup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strndup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"xstrdup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"memdup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"xmemdup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

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
  CredentialCleanTrackRuleParser ConfigParser{*Mgr};
  std::string Option{"Config"};
  StringRef ConfigFile =
      Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
  std::optional<TaintConfiguration> Config =
      getConfiguration<TaintConfiguration>(*Mgr, this, Option, ConfigFile);
  if (!Config) {
    // We don't have external taint config, no parsing required.
    DynamicTaintRules = RuleLookupTy{};
    return;
  }

  CredentialCleanTrackRuleParser::RulesContTy Rules{
      ConfigParser.parseConfiguration(Option, std::move(*Config))};

  DynamicTaintRules.emplace(std::make_move_iterator(Rules.begin()),
                            std::make_move_iterator(Rules.end()));
}



// check memset/free function
void CredentialCleanTrackChecker::checkPreCall(const CallEvent &Call,
                                       CheckerContext &C) const {
  
    if(cc_doutput_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"DOutput"};
        cc_doutput_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_doutput_path,std::ios::out);
        file.close();
    }
    if(cc_other_output_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"OOutput"};
        cc_other_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_other_output_path,std::ios::out);
        file.close();
    }

    std::ofstream debugfile;
    debugfile.open(cc_doutput_path,std::ios::app);

    debugfile << "\n----checkPreCall----\n";
    llvm::dbgs() << "\n----checkPreCall----\n";
    if (Call.getCalleeIdentifier()){
        debugfile << Call.getCalleeIdentifier()->getName().str() << "\n";
        llvm::dbgs() << Call.getCalleeIdentifier()->getName().str() << "\n";
    }

    debugfile << "\n";
    
    std::string debug = "";
    llvm::raw_string_ostream doutput(debug);
    Call.dump(doutput);
    C.getStackFrame()->dumpStack(doutput);
    debugfile << debug << "\n";
    Call.dump(llvm::dbgs());
    llvm::dbgs() << "\n";

    initTaintRules(C);

    ProgramStateRef State = C.getState();
    auto &F = State->getStateManager().get_context<TaintTagSet>();


    debug = "";
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << debug << "\n++++++++++++++\n";

    
    debug = "";
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << debug << "\n++++++++++++++\n";
        

    if (const auto *Rule = Call.isGlobalCFunction() ? StaticTaintRules->lookup(Call) : nullptr){
        debugfile << "Global Taint Rule Matched!\n";
        // debugfile.close();
        debug = "";
        Rule->process(*this, Call, C, doutput);
        debugfile << debug << "\n";
    }
    else if (const auto *Rule = DynamicTaintRules->lookup(Call)){
        debugfile << "Dynamic Taint Rule Matched!\n";
        // debugfile.close();
        debug = "";
        Rule->process(*this, Call, C, doutput);
        debugfile << debug << "\n";
    }

    debugfile << "\n----checkPreCall End ----\n";
    if (Call.getCalleeIdentifier()){
        debugfile << Call.getCalleeIdentifier()->getName().str() << "\n";
        llvm::dbgs() << Call.getCalleeIdentifier()->getName().str() << "\n";
    }
    debugfile.close();
    
    

}

void CredentialCleanTrackChecker::checkPostCall(const CallEvent &Call,
                                        CheckerContext &C) const {
  
    if(cc_doutput_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"DOutput"};
        cc_doutput_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_doutput_path,std::ios::out);
        file.close();
    }
    if(cc_other_output_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"OOutput"};
        cc_other_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_other_output_path,std::ios::out);
        file.close();
    }

    std::ofstream debugfile;
    debugfile.open(cc_doutput_path,std::ios::app);

    debugfile << "\n----checkPostCall----\n";
    if (Call.getCalleeIdentifier()){
        debugfile << Call.getCalleeIdentifier()->getName().str() << "\n";
        llvm::dbgs() << Call.getCalleeIdentifier()->getName().str() << "\n";
    }

    // Set the marked values as tainted. The return value only accessible from
    // checkPostStmt.
    ProgramStateRef State = C.getState();
    const StackFrameContext *CurrentFrame = C.getStackFrame();


    std::string debug = "";
    llvm::raw_string_ostream doutput(debug);
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << debug << "\n++++++++++++++\n";

    // Depending on what was tainted at pre-visit, we determined a set of
    // arguments which should be tainted after the function returns. These are
    // stored in the state as TaintArgsOnPostVisit set.

    // TaintArgsOnPostVisitTy TaintArgsMap = State->get<TaintArgsOnPostVisit>();
    // const ImmutableSet<ArgIdxTy> *TaintArgs = TaintArgsMap.lookup(CurrentFrame);

    // if (!TaintArgs)
    //   return;
    // assert(!TaintArgs->isEmpty());

    TaintArgsOnPostVisitTy TaintArgsMap = State->get<TaintArgsOnPostVisit>();

    const ImmutableSet<ArgIdxTy> *TaintArgs_all = TaintArgsMap.lookup(CurrentFrame);
    if (!TaintArgs_all)
        return;
    assert(!TaintArgs_all->isEmpty());

    TaintTagsOnPostVisitTy TaintTagsMap = State->get<TaintTagsOnPostVisit>();

    const ImmutableSet<TaintTagType> *TaintTags_all = TaintTagsMap.lookup(CurrentFrame);
    if (!TaintTags_all)
        return;
    assert(!TaintTags_all->isEmpty());

    auto &F = State->getStateManager().get_context<ArgIdxFactory>();
    auto &FF = State->getStateManager().get_context<TaintTagSet>();

    ImmutableSet<ArgIdxTy> TaintArgs = F.getEmptySet();
    ImmutableSet<TaintTagType> TaintTags = FF.getEmptySet();
    int len = 0, i = 0;
    debugfile << "\n TaintTagsMap: ";
    for(ImmutableSet<TaintTagType>::iterator TI = TaintTags_all->begin(), TE = TaintTags_all->end(); TI != TE; ++TI){
        debugfile << *TI << " ";
        TaintTags = FF.add(TaintTags, *TI);
    }

    if (TaintTags.isEmpty())
        return;
    assert(!TaintTags.isEmpty());

    debugfile << "\n TaintArgsMap: ";
    for(ImmutableSet<ArgIdxTy>::iterator TI = TaintArgs_all->begin(), TE = TaintArgs_all->end(); TI != TE; ++TI){
        debugfile << *TI << " ";
        TaintArgs = F.add(TaintArgs, *TI);
    }

    debugfile << "\n";


    if (TaintArgs.isEmpty())
        return;
    assert(!TaintArgs.isEmpty());


    for (ArgIdxTy ArgNum : TaintArgs) {
        debugfile << "\n\nPostCall<";
        debug = "";
        Call.dump(doutput);
        debugfile << debug;
        debugfile << "> actually wants to taint arg index: " << ArgNum << "\n";

        for (TaintTagType tag : TaintTags){
            debugfile << "\ntag = " << tag;
            llvm::dbgs() << "tag = " << tag << "\n";

            // Special handling for the tainted return value.
            if (ArgNum == ReturnValueIndex) {
                SVal KeySVal = Call.getReturnValue();
                // const Expr * E = Call.getArgExpr(ArgNum);
                if(!KeySVal.getAs<Loc>())
                    continue;
                debug = "";
                KeySVal.dumpToStream(doutput);
                debugfile << "\nSVAL = " << debug << "\n";
                // State = addCredVar(State, KeySVal, tag + TaintTagRet);
                State = addCredVar(State, KeySVal, tag);
                State = addCredVar(State, KeySVal, TaintTagRet);
                continue;
            }
            
            SVal KeySVal = Call.getArgSVal(ArgNum);
            // const Expr * E = Call.getArgExpr(ArgNum);
            if(!KeySVal.getAs<Loc>())
                continue;
            // if(const auto *PSVal = getPointeeOrPointer(State, KeySVal))
            if(auto PSVal = getPointeeOrPointer(State, KeySVal)){
              debugfile << "This is a Pointer\n";
              debug = "";
              PSVal->dumpToStream(doutput);
              debugfile << "\nSVAL = " << debug << "\n";
              State = addCredVar(State, *PSVal, tag);
            }else{
              State = addCredVar(State, *PSVal, tag);
            }
            
        }
    }

    debug = "";
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << debug << "\n++++++++++++++\n";

    

    // Clear up the taint info from the state.
    State = State->remove<TaintArgsOnPostVisit>(CurrentFrame);
    State = State->remove<TaintTagsOnPostVisit>(CurrentFrame);
    C.addTransition(State);
    // C.addTransition(State, C.getPredecessor());
    debugfile << "\n----checkPostCall End ----\n";
    if (Call.getCalleeIdentifier()){
        debugfile << Call.getCalleeIdentifier()->getName().str() << "\n";
    }
    debugfile.close();
}


void CredentialCleanTrackChecker::checkPostStmt(const DeclStmt *DS,
                                        CheckerContext &C) const {
    
    if(cc_doutput_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"DOutput"};
        cc_doutput_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_doutput_path,std::ios::out);
        file.close();
    }
    if(cc_other_output_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"OOutput"};
        cc_other_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_other_output_path,std::ios::out);
        file.close();
    }


    ProgramStateRef State = C.getState();
    const StackFrameContext *CurrentFrame = C.getStackFrame();

    auto &F = State->getStateManager().get_context<TaintTagSet>();

    std::ofstream debugfile;
    debugfile.open(cc_doutput_path,std::ios::app);

    debugfile << "\n----checkPostStmt: DeclStmt ----\n\n";
    std::string debug = "";
    llvm::raw_string_ostream doutput(debug);
    DS->dump(doutput, C.getASTContext());
    debugfile << debug << "\n";
    bool isAdd = false;


    if(const Decl * D = DS->getSingleDecl()){
        if(const VarDecl *VD = dyn_cast_or_null<VarDecl>(D)){
            const string var_name = str2lower(VD->getNameAsString());
            if(var_name.find("pass") != std::string::npos){
                if(const ImplicitCastExpr *ICE = dyn_cast_or_null<ImplicitCastExpr>(VD->getInit())){
                    if(const CallExpr *CE = dyn_cast_or_null<CallExpr>(ICE->getSubExpr())){
                        debugfile << "\nThe Right is CallExpr\n";

                        SVal S = C.getSVal(CE);
                        if(!S.isUnknown() && S.getAs<Loc>()){
                            auto PSVal = getPointeeOrPointer(State, S);
                            debug = "";
                            PSVal->dumpToStream(doutput);
                            debugfile << "\nPSVal = " << debug << "\n";
                            debug = "";
                            S.dumpToStream(doutput);
                            debugfile << "\nSVal = " << debug << "\n";
                            State = addTaintedCallExprRet(State, *PSVal, C);
                            isAdd = true;
                        }
                        // }
                        // }
                    }
                    if(const DeclRefExpr * DRE = dyn_cast_or_null<DeclRefExpr>(ICE->getSubExpr())){
                        debugfile << "\nThe Right is DeclRefExpr\n";
                        // ) && (!C.getSVal(DRE)->isUnknown())
                        SVal S = C.getSVal(DRE);
                        if(!S.isUnknown() && S.getAs<Loc>()){
                            auto PSVal = getPointeeOrPointer(State, S);
                            debug = "";
                            PSVal->dumpToStream(doutput);
                            debugfile << "\nSVAL = " << debug << "\n";
                            State = addCredVar(State, *PSVal, TaintTagCred);
                            isAdd = true;
                        }
                    }
                    if(isAdd == false){
                        debugfile << "\nThe Right is other (ImplicitCastExpr)\n";
                        SVal S = C.getSVal(ICE);
                        if(!S.isUnknown() && S.getAs<Loc>()){
                            auto PSVal = getPointeeOrPointer(State, S);
                            debug = "";
                            PSVal->dumpToStream(doutput);
                            debugfile << "\nPSVal = " << debug << "\n";
                            debug = "";
                            S.dumpToStream(doutput);
                            debugfile << "\nSVal = " << debug << "\n";
                            State = addCredVar(State, *PSVal, TaintTagCred);
                        }
                    }
                }
            }
            
        }
    }


    C.addTransition(State);

    debug = "";
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << debug << "\n++++++++++++++\n";

    debugfile << "\n----checkPostStmt: DeclStmt End ----\n\n";
    debugfile.close();

}


void CredentialCleanTrackChecker::checkPreStmt(const BinaryOperator *BO,
                                        CheckerContext &C) const {
  
    if(cc_doutput_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"DOutput"};
        cc_doutput_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_doutput_path,std::ios::out);
        file.close();
    }
    if(cc_other_output_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"OOutput"};
        cc_other_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_other_output_path,std::ios::out);
        file.close();
    }


    ProgramStateRef State = C.getState();
    const StackFrameContext *CurrentFrame = C.getStackFrame();
    BinaryOperatorKind OK = BO->getOpcode();
    if (!BO->isAssignmentOp()){
        return;
    }

    auto &F = State->getStateManager().get_context<TaintTagSet>();

    std::ofstream debugfile;
    debugfile.open(cc_doutput_path,std::ios::app);

    debugfile << "\n----checkPreStmt: BinaryOperator ----\n\n";
    std::string debug = "";
    llvm::raw_string_ostream doutput(debug);
    BO->dump(doutput, C.getASTContext());
    debugfile << debug << "\n";


    TaintTagType tagvalue = 0;
    SVal RVal = State->getSVal(BO->getRHS(), C.getLocationContext());
    SVal LVal = State->getSVal(BO->getLHS(), C.getLocationContext());
    debugfile << "\n++++++++++++++++ LVal\n";
    std::string debugl = "";
    llvm::raw_string_ostream doutputl(debugl);
    LVal.dumpToStream(doutputl);
    debugfile << debugl << "\n";
    debugfile << "\n++++++++++++++++ RVal\n";
    std::string debugr = "";
    llvm::raw_string_ostream doutputr(debugr);
    RVal.dumpToStream(doutputr);
    debugfile << debugr << "\n";
    RVal.dumpToStream(llvm::dbgs());
    

    debug = "";
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << debug << "\n++++++++++++++\n";

    if(isCredentialVar(BO->getLHS()) && LVal.getAs<Loc>()){
        debugfile << "\nLeft variable is password variable!\n";
        auto PSVal = getPointeeOrPointer(State, LVal);
        debugl = "";
        PSVal->dumpToStream(doutputl);
        debugfile << debugl << "\n";
        State = removeCredVar(State, *PSVal);
    }
    
    C.addTransition(State);

    debug = "";
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << debug << "\n++++++++++++++\n";

    debugfile << "\n----checkPreStmt: BinaryOperator End ----\n\n";
    debugfile.close();

}


// password = getenv("xxx")
// password = optarg
// password = open(xxx)
void CredentialCleanTrackChecker::checkPostStmt(const BinaryOperator *BO,
                                        CheckerContext &C) const {
  
    if(cc_doutput_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"DOutput"};
        cc_doutput_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_doutput_path,std::ios::out);
        file.close();
    }
    if(cc_other_output_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"OOutput"};
        cc_other_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_other_output_path,std::ios::out);
        file.close();
    }


    ProgramStateRef State = C.getState();
    const StackFrameContext *CurrentFrame = C.getStackFrame();
    BinaryOperatorKind OK = BO->getOpcode();
    if (!BO->isAssignmentOp()){
        return;
    }

    auto &F = State->getStateManager().get_context<TaintTagSet>();

    std::ofstream debugfile;
    debugfile.open(cc_doutput_path,std::ios::app);

    debugfile << "\n----checkPostStmt: BinaryOperator ----\n\n";
    std::string debug = "";
    llvm::raw_string_ostream doutput(debug);
    BO->dump(doutput, C.getASTContext());
    debugfile << debug << "\n";


    TaintTagType tagvalue = 0;
    SVal RVal = State->getSVal(BO->getRHS(), C.getLocationContext());
    SVal LVal = State->getSVal(BO->getLHS(), C.getLocationContext());
    debugfile << "\n++++++++++++++++ LVal\n";
    std::string debugl = "";
    llvm::raw_string_ostream doutputl(debugl);
    LVal.dumpToStream(doutputl);
    debugfile << debugl << "\n";
    debugfile << "\n++++++++++++++++ RVal\n";
    std::string debugr = "";
    llvm::raw_string_ostream doutputr(debugr);
    RVal.dumpToStream(doutputr);
    debugfile << debugr << "\n";
    RVal.dumpToStream(llvm::dbgs());
    // RVal.getAsSymbol()->dumpToStream(llvm::dbgs());


    debug = "";
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << debug << "\n++++++++++++++\n";

    if(isCredentialVar(BO->getLHS()) && LVal.getAs<Loc>()){
        if(const ImplicitCastExpr *ICE = dyn_cast_or_null<ImplicitCastExpr>(BO->getRHS())){
            debugfile << "\nRight is ImplicitCastExpr\n";
            if(const CallExpr *CE = dyn_cast_or_null<CallExpr>(ICE)){
                debugfile << "\nRight is Call expression\n";
                SVal S = C.getSVal(CE);
                if(S.getAs<Loc>()){
                    auto PSVal = getPointeeOrPointer(State, S);
                    debug = "";
                    PSVal->dumpToStream(doutput);
                    debugfile << "\nSVAL = " << debug << "\n";
                    State = addTaintedCallExprRet(State, *PSVal, C);
                }
            }
            else{
                if(RVal.getAs<Loc>()){
                    auto PSVal = getPointeeOrPointer(State, RVal);
                    debug = "";
                    PSVal->dumpToStream(doutput);
                    debugfile << "\nRVAL = " << debug << "\n";
                    State = addCredVar(State, *PSVal, TaintTagCred);
                    // auto PSLVal = getPointeeOrPointer(State, LVal);
                    // State = removeCredVar(State, PSLVal);
                }
            }
        }
        else{
            if(RVal.getAs<Loc>()){
                auto PSVal = getPointeeOrPointer(State, RVal);
                debug = "";
                PSVal->dumpToStream(doutput);
                debugfile << "\nRVAL = " << debug << "\n";
                State = addCredVar(State, *PSVal, TaintTagCred);
                // auto PSLVal = getPointeeOrPointer(State, LVal);
                // State = removeCredVar(State, PSLVal);
            }
        }

    }
    
    C.addTransition(State);

    debug = "";
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << debug << "\n++++++++++++++\n";

    debugfile << "\n----checkPostStmt: BinaryOperator End ----\n\n";
    debugfile.close();

}

void CredentialCleanTrackChecker::checkDeadSymbols(SymbolReaper & SymReaper , CheckerContext & C ) const{
    if(cc_doutput_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"DOutput"};
        cc_doutput_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_doutput_path,std::ios::out);
        file.close();
    }
    if(cc_other_output_path == ""){
        CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
        assert(Mgr);
        std::string Option{"OOutput"};
        cc_other_output_path = Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
        std::ofstream file;
        file.open(cc_other_output_path,std::ios::out);
        file.close();
    }


    ProgramStateRef State = C.getState();
    // const StackFrameContext *CurrentFrame = C.getStackFrame();

    std::ofstream debugfile;
    debugfile.open(cc_doutput_path,std::ios::app);

    debugfile << "\n----checkDeadSymbols: ----\n\n";
    std::string debug = "";
    llvm::raw_string_ostream doutput(debug);
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << debug << "\n++++++++++++++\n";

    ImmutableMap<SymbolRef, TaintTagSet> TS = State->get<CredSymbolMap>();

    // debugfile << "\n++++++++++++++\n" << "1State = " << State->getID() << "\n";

    for (ImmutableMap<SymbolRef, TaintTagSet>::iterator iter = TS.begin(); iter !=TS.end(); iter++)
    {
        std::string debugs = "";
        llvm::raw_string_ostream doutputs(debugs);
        iter->first->dumpToStream(doutputs);

        SymbolRef Sym = iter->first;
        bool IsSymDead = SymReaper.isDead(Sym);
        const TaintTagSet *T = State->get<CredSymbolMap>(Sym);
        // debugfile << "\n++++++++++++++\n" << "2State = " << State->getID() << "\n";
        
        if (IsSymDead && T && (count(T->begin(), T->end(), TaintTagCred)>0) && (count(T->begin(), T->end(), TaintTagCredMemset)<=0)) 
        {
            // debugfile << "\n++++++++++++++\n" << "3State = " << State->getID() << "\n";
            State = State->remove<CredSymbolMap>(Sym);
            if (State->get<ReportedSymbol>(Sym))
                continue;
            State = State->set<ReportedSymbol>(Sym, 1);
            // debugfile << "\n++++++++++++++\n" << "4State = " << State->getID() << "\n";
            // generateReportIfTainted1(Sym, nullptr, MsgCustomSinkNotMemset, C);
            if (ExplodedNode *N = C.generateErrorNode()) {
                auto report = std::make_unique<PathSensitiveBugReport>(BT, MsgCustomSinkNotMemset, N);
                C.emitReport(std::move(report));
            }
            // debugfile << "\n++++++++++++++\n" << "5State = " << State->getID() << "\n";
            debugfile << "There is a SymbolRef ("<< debugs << ") dead without being memset\n";
            continue;
        }
        else if (IsSymDead) {
            State = State->remove<CredSymbolMap>(Sym);
            State = State->remove<ReportedSymbol>(Sym);
        }
    }

    // debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n";

    ImmutableMap<const ElementRegion*, TaintTagSet> TR = State->get<CredRegionMap>();
    for (ImmutableMap<const ElementRegion*, TaintTagSet>::iterator iter = TR.begin(); iter !=TR.end(); iter++)
    {
        std::string debuge = "";
        llvm::raw_string_ostream doutpute(debuge);
        iter->first->dumpToStream(doutpute);

        const ElementRegion* region = iter->first;
        const TaintTagSet *T = State->get<CredRegionMap>(region);
        // bool IsSymDead = !SymReaper.isLive(region);
        bool IsRegDead = !SymReaper.isLiveRegion(region);
        if (IsRegDead && T && (count(T->begin(), T->end(), TaintTagCred)>0) && (count(T->begin(), T->end(), TaintTagCredMemset)<=0)) 
        {
            State = State->remove<CredRegionMap>(region);
            if (State->get<ReportedRegion>(region))
                continue;
            State = State->set<ReportedRegion>(region, 1);
            // generateReportIfTainted1(nullptr, region, MsgCustomSinkNotMemset, C);
            if (ExplodedNode *N = C.generateErrorNode()) {
                auto report = std::make_unique<PathSensitiveBugReport>(BT, MsgCustomSinkNotMemset, N);
                C.emitReport(std::move(report));
            }
            debugfile << "There is a ElementRegion ("<< debuge << ") dead without being memset\n";
            continue;
        }
        else if (IsRegDead){
            State = State->remove<CredRegionMap>(region);
            State = State->remove<ReportedRegion>(region);
        }
    }
    // debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n";

    C.addTransition(State);

    debug = "";
    // llvm::raw_string_ostream doutput(debug);
    printCredTaints(doutput, State);
    debugfile << "\n++++++++++++++\n" << "State = " << State->getID() << "\n" << "Pre State = " << C.getPredecessor()->getID() << "\n" << debug << "\n++++++++++++++\n";
    
    
    
    // C.addTransition(State, C.getPredecessor());

    debugfile << "\n----checkDeadSymbols End ----\n\n";
    debugfile.close();
}



void CredentialCleanTrackChecker::printState(raw_ostream &Out, ProgramStateRef State,
                                     const char *NL, const char *Sep) const {
  printTaint(State, Out, NL, Sep);
}

void CredentialCleanTrackChecker::printCredTaints(raw_ostream &Out, ProgramStateRef State) const {
  ImmutableMap<SymbolRef, TaintTagSet> TM = State->get<CredSymbolMap>();

  if (!TM.isEmpty())
    Out << "Tainted symbols:" << "\n";
  

  for(ImmutableMap<SymbolRef, TaintTagSet>::iterator I = TM.begin(), E = TM.end(); I != E; ++I) {
    Out << I->first << " : ";
    for(TaintTagSet::iterator IS = I->second.begin(), ES = I->second.end(); IS != ES; ++ IS)
      Out << (*IS) << ' ';
    Out << "\n";
  }
  
  ImmutableMap<const ElementRegion *, TaintTagSet> TRM = State->get<CredRegionMap>();
  if (!TRM.isEmpty())
    Out << "Tainted Element Region:" << "\n";
  
  for(ImmutableMap<const ElementRegion *, TaintTagSet>::iterator I = TRM.begin(), E = TRM.end(); I != E; ++I) {
    Out << I->first << " : ";
    for(TaintTagSet::iterator IS = I->second.begin(), ES = I->second.end(); IS != ES; ++ IS)
      Out << (*IS) << ' ';
    Out << "\n";
  }
}


void CredentialCleanTrackRule::process(const CredentialCleanTrackChecker &Checker,
                               const CallEvent &Call, CheckerContext &C, raw_ostream &debugfile) const {
  ProgramStateRef State = C.getState();
  const ArgIdxTy CallNumArgs = fromArgumentCount(Call.getNumArgs());

  // std::ofstream debugfile;
  // debugfile.open(cc_doutput_path,std::ios::app);
  

  /// Iterate every call argument, and get their corresponding Expr and SVal.
  const auto ForEachCallArg = [&C, &Call, CallNumArgs](auto &&Fun) {
    for (ArgIdxTy I = ReturnValueIndex; I < CallNumArgs; ++I) {
      const Expr *E = GetArgExpr(I, Call);
      Fun(I, E, C.getSVal(E));
    }
  };

  /// Check for taint filters. (decryption-related functions)
  ForEachCallArg([this, &C, &State](ArgIdxTy I, const Expr *E, SVal S) {
    if (FilterArgs.contains(I)) {
      State = removeTaint(State, S);
      if (auto P = getPointeeOf(State, S))
        State = removeTaint(State, *P);
    }
  });

  /// Check for taint propagation sources.
  /// A rule is relevant if PropSrcArgs is empty, or if any of its signified
  /// args are tainted in context of the current CallEvent.
  bool IsMatching = PropSrcArgs.isEmpty();
  ForEachCallArg(
      [this, &C, &Checker, &IsMatching, &State, &debugfile](ArgIdxTy I, const Expr *E, SVal S) {
        IsMatching = IsMatching || (PropSrcArgs.contains(I) &&
                                    Checker.isTaintedOrPointsToTainted1(S, State, C));
        debugfile << "For taint propagation: Indx = " << I << ", PropSrcArgs = " << PropSrcArgs.contains(I) << ", IsTainted = " << (PropSrcArgs.contains(I) && Checker.isTaintedOrPointsToTainted1(S, State, C)) << "\n";
  });

  debugfile << "\nIsMatching = " << IsMatching << "\n";

  if (!IsMatching){
    // debugfile.close();
    return;
  }

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
  ImmutableSet<ArgIdxTy> Result_args = F.getEmptySet();
  auto &FF = State->getStateManager().get_context<TaintTagSet>();
  ImmutableSet<TaintTagType> Result_tags = FF.getEmptySet();

  bool IsTaintedMemset = false;
  bool IsTaintedFree = false;
  bool IsCred = false;
  ForEachCallArg(
      [this, &C, &Checker, &IsTaintedMemset, &IsTaintedFree, &IsCred, &State, &debugfile](ArgIdxTy I, const Expr *E, SVal S) {
        IsTaintedMemset = IsTaintedMemset || (PropSrcArgs.contains(I) && Checker.isTaintedOrPointsToTainted1(S, State, C, TaintTagCredMemset)) || (SourceArgs.contains(I) && SrcMsg.value() == TaintTagCredMemset);
        IsTaintedFree = IsTaintedFree || (PropSrcArgs.contains(I) && Checker.isTaintedOrPointsToTainted1(S, State, C, TaintTagCredFree)) || (SourceArgs.contains(I) && SrcMsg.value() == TaintTagCredFree);
        IsCred = IsCred || (PropSrcArgs.contains(I) && Checker.isTaintedOrPointsToTainted1(S, State, C, TaintTagCred)) || (SourceArgs.contains(I) && SrcMsg.value() == TaintTagCred);
  });

  debugfile << "\nIsTaintedMemset = " << IsTaintedMemset << "; IsTaintedFree = " << IsTaintedFree << "; IsCred = " << IsCred << "\n";

  if(IsTaintedMemset){
    Result_tags = FF.add(Result_tags, TaintTagCredMemset);
  }
  if(IsTaintedFree){
    Result_tags = FF.add(Result_tags, TaintTagCredFree);
  }
  if(IsCred){
    Result_tags = FF.add(Result_tags, TaintTagCred);
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
          Result_args = F.add(Result_args, I);
        }

        if (PropDstArgs.contains(I)) {
          LLVM_DEBUG(llvm::dbgs() << "PreCall<"; Call.dump(llvm::dbgs());
                     llvm::dbgs() << "> prepares tainting arg index: " << I << '\n';);

          debugfile << "\nPreCall PropDstArgs<";
          std::string debug = "";
          llvm::raw_string_ostream doutput(debug);
          Call.dump(doutput);
          debugfile << debug;
          debugfile << "> prepares tainting arg index: " << I << '\n';

          Result_args = F.add(Result_args, I);
        }

        // TODO: We should traverse all reachable memory regions via the
        // escaping parameter. Instead of doing that we simply mark only the
        // referred memory region as tainted.
        if (WouldEscape(V, E->getType())) {
          LLVM_DEBUG(if (!Result_args.contains(I)) {
            llvm::dbgs() << "PreCall<";
            Call.dump(llvm::dbgs());
            llvm::dbgs() << "> prepares tainting arg index: " << I << '\n';
          });

          debugfile << "\nPreCall<";
          std::string debug = "";
          llvm::raw_string_ostream doutput(debug);
          Call.dump(doutput);
          debugfile << debug << "\n";
          debugfile << "> prepares tainting arg index: " << I << '\n';

          Result_args = F.add(Result_args, I);
        }
      });
    
  // debugfile.close();
  if (!Result_args.isEmpty())
    State = State->set<TaintArgsOnPostVisit>(C.getStackFrame(), Result_args);
  if (!Result_tags.isEmpty())
    State = State->set<TaintTagsOnPostVisit>(C.getStackFrame(), Result_tags);
  C.addTransition(State);
  // return State;
}

bool CredentialCleanTrackChecker::generateReportIfTainted(const Expr *E, StringRef Msg,
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

bool CredentialCleanTrackChecker::generateReportIfTainted1(SymbolRef Sym, const ElementRegion *ER, StringRef Msg,
                                                  CheckerContext &C) const {

  // Generate diagnostic.
  if (ExplodedNode *N = C.generateNonFatalErrorNode()) {
    auto report = std::make_unique<PathSensitiveBugReport>(BT, Msg, N);
    if(Sym){
        report->addVisitor(std::make_unique<CredCleanBugVisitor>(Sym, nullptr, 0));
    }else{
        report->addVisitor(std::make_unique<CredCleanBugVisitor>(nullptr, ER, 0));
    }
    C.emitReport(std::move(report));
    return true;
  }
  return false;
}


bool CredentialCleanTrackChecker::isTaintedOrPointsToTainted1(SVal S, const ProgramStateRef &State, CheckerContext &C, TaintTagType tag) const {
    
    llvm::dbgs() << "\n------------- isTaintedOrPointsToTainted1 ----------------\n";
    if(tag == TaintTagNone){
        if(checkCredVar(State, S, TaintTagCred) || checkCredVar(State, S, TaintTagCredFree) || checkCredVar(State, S, TaintTagCredMemset)){
            return true;
        }
    }
    else if(tag == TaintTagRet){
        if(checkCredVar(State, S, TaintTagCredRet) || checkCredVar(State, S, TaintTagCredFreeRet) || checkCredVar(State, S, TaintTagCredMemsetRet)){
            return true;
        }
    }
    else{
        return checkCredVar(State, S, tag);
    }
    return false;
}

ProgramStateRef CredentialCleanTrackChecker::addTaintedCallExprRet(ProgramStateRef &State, SVal S, CheckerContext &C) const {
    
    llvm::dbgs() << "\n------------- addTaintedCallExprRet ----------------\n";
    if(checkCredVar(State, S, TaintTagCredRet)){
        State = addCredVar(State, S, TaintTagCred);
    }
    if(checkCredVar(State, S, TaintTagCredFreeRet)){
        State = addCredVar(State, S, TaintTagCredFree);
    }
    if(checkCredVar(State, S, TaintTagCredMemsetRet)){
        State = addCredVar(State, S, TaintTagCredMemset);
    }
    return State;
}

ProgramStateRef CredentialCleanTrackChecker::addCredVar(ProgramStateRef State, SVal V, TaintTagType Kind) const{
    llvm::dbgs() << "\n------------- addCredVar SVal ----------------\n";
    llvm::dbgs() << "\n++++++++++++++\n";
    V.dumpToStream(llvm::dbgs());
    llvm::dbgs() << "\n++++++++++++++\n";
    SymbolRef Sym = V.getAsSymbol();
    if(Sym){
        State = addCredVar(State, Sym, Kind);
    }

    if (auto LCV = V.getAs<nonloc::LazyCompoundVal>()) {
        if (std::optional<SVal> binding = State->getStateManager().getStoreManager().getDefaultBinding(*LCV)) {
            if (SymbolRef Sym = binding->getAsSymbol())
                State = addPartialCredVar(State, Sym, LCV->getRegion(), Kind);
        }
    }

    const MemRegion *R = V.getAsRegion();
    State = addCredVar(State, R, Kind);

    llvm::dbgs() << "\n------------- addCredVar SVal end ----------------\n";
    return State;

}


ProgramStateRef CredentialCleanTrackChecker::addCredVar(ProgramStateRef State, SymbolRef Sym, TaintTagType Kind) const{
    llvm::dbgs() << "\n------------- addCredVar SymbolRef ----------------\n";
    auto &F = State->getStateManager().get_context<TaintTagSet>();
    if (Sym)
    {   
        llvm::dbgs() << "\n++++++++++++++\n";
        Sym->dumpToStream(llvm::dbgs());
        llvm::dbgs() << "\n++++++++++++++\n";
        while (const SymbolCast *SC = dyn_cast<SymbolCast>(Sym))
            Sym = SC->getOperand();
        
        llvm::dbgs() << "\n++++++++++++++\n";
        Sym->dumpToStream(llvm::dbgs());
        llvm::dbgs() << "\n++++++++++++++\n";

        const TaintTagSet *T = State->get<CredSymbolMap>(Sym);
        TaintTagSet tags = T ? *T : F.getEmptySet();
        if(!T || (T && count(T->begin(), T->end(), Kind)<=0)){
            tags = F.add(tags, Kind);
            State = State->set<CredSymbolMap>(Sym, tags);
        }
    }
    return State;
}


ProgramStateRef CredentialCleanTrackChecker::addCredVar(ProgramStateRef State, const MemRegion *R, TaintTagType Kind) const{
    if(!R)
        return State;

    llvm::dbgs() << "\n------------- addCredVar MemRegion ----------------\n";
    auto &F = State->getStateManager().get_context<TaintTagSet>();
    llvm::dbgs() << "\n++++++++++++++\n";
    R->dumpToStream(llvm::dbgs());
    llvm::dbgs() << "\n++++++++++++++\n";
    if (const ElementRegion *ER = dyn_cast<ElementRegion>(R)){
        const TaintTagSet *T = State->get<CredRegionMap>(ER);
        TaintTagSet tags = T ? *T : F.getEmptySet();
        if(!T || (T && count(T->begin(), T->end(), Kind)<=0)){
            tags = F.add(tags, Kind);
            State = State->set<CredRegionMap>(ER, tags);
        }
    }else if (const SymbolicRegion *SR = dyn_cast_or_null<SymbolicRegion>(R)){
        State = addCredVar(State, SR->getSymbol(), Kind);
    }
    return State;
}

ProgramStateRef CredentialCleanTrackChecker::addPartialCredVar(ProgramStateRef State, SymbolRef ParentSym, const SubRegion *SubRegion, TaintTagType Kind) const {
    llvm::dbgs() << "\n------------- addPartialCredVar ----------------\n";
    llvm::dbgs() << "\n++++++++++++++\n";
    ParentSym->dumpToStream(llvm::dbgs());
    SubRegion->dumpToStream(llvm::dbgs());
    llvm::dbgs() << "\n++++++++++++++\n";
    if (const TaintTagSet *T = State->get<CredSymbolMap>(ParentSym))
        if (T && (count(T->begin(), T->end(), Kind)>0))
            return State;
    
    if (SubRegion == SubRegion->getBaseRegion())
        return addCredVar(State, ParentSym, Kind);
    
    const TaintedSubRegions *SavedRegs = State->get<CredDerivedSymbolMap>(ParentSym);
    TaintedSubRegions::Factory &F = State->get_context<TaintedSubRegions>();
    auto &TF = State->getStateManager().get_context<TaintTagSet>();
    TaintedSubRegions Regs = SavedRegs ? *SavedRegs : F.getEmptyMap();
    TaintTagSet Tags = Regs.contains(SubRegion) ? *(Regs.lookup(SubRegion)) : TF.getEmptySet();

    Tags = TF.add(Tags, Kind);
    Regs = F.add(Regs, SubRegion, Tags);
    ProgramStateRef NewState = State->set<CredDerivedSymbolMap>(ParentSym, Regs);
    return NewState;
}

ProgramStateRef CredentialCleanTrackChecker::removeCredVar(ProgramStateRef State, SVal V) const {
    llvm::dbgs() << "\n------------- removeCredVar ----------------\n";
    llvm::dbgs() << "\n++++++++++++++\n";
    V.dumpToStream(llvm::dbgs());
    llvm::dbgs() << "\n++++++++++++++\n";
    SymbolRef Sym = V.getAsSymbol();
    if(Sym){
        State = removeCredVar(State, Sym);
    }

    const MemRegion *R = V.getAsRegion();
    if(R)
      State = removeCredVar(State, R);

    llvm::dbgs() << "\n------------- removeCredVar SVal end ----------------\n";
    return State;
}

ProgramStateRef CredentialCleanTrackChecker::removeCredVar(ProgramStateRef State, const MemRegion *R) const {
    if(!R)
        return State;
    
    llvm::dbgs() << "\n------------- removeCredVar MemRegion ----------------\n";
    llvm::dbgs() << "\n++++++++++++++\n";
    R->dumpToStream(llvm::dbgs());
    llvm::dbgs() << "\n++++++++++++++\n";

    if (const ElementRegion *ER = dyn_cast<ElementRegion>(R)){
        State = State->remove<CredRegionMap>(ER);
    }
    
    if (const SymbolicRegion *SR = dyn_cast_or_null<SymbolicRegion>(R)){
        State = removeCredVar(State, SR->getSymbol());
    }

    llvm::dbgs() << "\n------------- removeCredVar MemRegion end ----------------\n";
    return State;
}

ProgramStateRef CredentialCleanTrackChecker::removeCredVar(ProgramStateRef State, SymbolRef Sym) const {
    llvm::dbgs() << "\n------------- removeCredVar SymbolRef ----------------\n";
    llvm::dbgs() << "\n++++++++++++++\n";
    Sym->dumpToStream(llvm::dbgs());
    llvm::dbgs() << "\n++++++++++++++\n";

    while (const SymbolCast *SC = dyn_cast<SymbolCast>(Sym))
        Sym = SC->getOperand();

    State = State->remove<CredSymbolMap>(Sym);

    llvm::dbgs() << "\n------------- removeCredVar SymbolRef end ----------------\n";
    return State;
}

bool CredentialCleanTrackChecker::checkCredVar(ProgramStateRef State, SVal V, TaintTagType Kind) const {
    llvm::dbgs() << "\n------------- checkCredVar SVal ----------------\n";
    llvm::dbgs() << "\n++++++++++++++\n";
    V.dumpToStream(llvm::dbgs());
    llvm::dbgs() << "\n++++++++++++++\n";

    SymbolRef Sym = V.getAsSymbol();
    if (Sym)
    {
        return checkCredVar(State, Sym, Kind);
    }else if(const MemRegion *R = V.getAsRegion()){
        return checkCredVar(State, R, Kind);
    }
    return false;
}

bool CredentialCleanTrackChecker::checkCredVar(ProgramStateRef State, SymbolRef Sym, TaintTagType Kind) const {
    llvm::dbgs() << "\n------------- checkCredVar Sym ----------------\n";
    llvm::dbgs() << "\n++++++++++++++\n";
    Sym->dumpToStream(llvm::dbgs());
    llvm::dbgs() << "\n++++++++++++++\n";

    if (Sym)
    {
        const TaintTagSet *T = State->get<CredSymbolMap>(Sym);
        if(T && (count(T->begin(), T->end(), Kind) > 0)){
            return true;
        }
    }

    if (!Sym)
        return false;

    // Traverse all the symbols this symbol depends on to see if any are tainted.
    // for (SymExpr::symbol_iterator SI = Sym->symbol_begin(), SE = Sym->symbol_end(); SI != SE; ++SI) {
    for (SymbolRef SubSym : Sym->symbols()) {
        if (!isa<SymbolData>(SubSym))
            continue;

        const TaintTagSet *T = State->get<CredSymbolMap>(SubSym);
        if(T && (count(T->begin(), T->end(), Kind) > 0)){
            return true;
        }

        if (const auto *SD = dyn_cast<SymbolDerived>(SubSym)) {
            // If this is a SymbolDerived with a tainted parent, it's also tainted.
            if (checkCredVar(State, SD->getParentSymbol(), Kind))
                return true;

            // If this is a SymbolDerived with the same parent symbol as another
            // tainted SymbolDerived and a region that's a sub-region of that tainted
            // symbol, it's also tainted.
            if (const TaintedSubRegions *Regs = State->get<CredDerivedSymbolMap>(SD->getParentSymbol())) {
                const TypedValueRegion *R = SD->getRegion();
                for (auto I : *Regs) {
                    // FIXME: The logic to identify tainted regions could be more
                    // complete. For example, this would not currently identify
                    // overlapping fields in a union as tainted. To identify this we can
                    // check for overlapping/nested byte offsets.

                     const TaintTagSet T = I.second;
                    if(!T.isEmpty() && (count(T.begin(), T.end(), Kind) > 0) && R->isSubRegionOf(I.first)){
                        return true;
                    }
                }
            }
        }

        // If memory region is tainted, data is also tainted.
        if (const auto *SRV = dyn_cast<SymbolRegionValue>(SubSym)) {
            if (checkCredVar(State, SRV->getRegion(), Kind))
                return true;
        }

        // If this is a SymbolCast from a tainted value, it's also tainted.
        if (const auto *SC = dyn_cast<SymbolCast>(SubSym)) {
            if (checkCredVar(State, SC->getOperand(), Kind))
                return true;
        }
    }

    return false;
}

bool CredentialCleanTrackChecker::checkCredVar(ProgramStateRef State, const MemRegion *R, TaintTagType Kind) const {
    if (!R)
        return false;

    llvm::dbgs() << "\n------------- checkCredVar MemRegion ----------------\n";
    llvm::dbgs() << "\n++++++++++++++\n";
    R->dumpToStream(llvm::dbgs());
    llvm::dbgs() << "\n++++++++++++++\n";

    // Element region (array element) is tainted if either the base or the offset
    // are tainted.
    if (const ElementRegion *ER = dyn_cast<ElementRegion>(R)){
        const TaintTagSet *T = State->get<CredRegionMap>(ER);
        if(T && (count(T->begin(), T->end(), Kind)) > 0){
            return true;
        }
        return checkCredVar(State, ER->getSuperRegion(), Kind) ||
            checkCredVar(State, ER->getIndex(), Kind);
    }
        
    if (const SymbolicRegion *SR = dyn_cast<SymbolicRegion>(R))
        return checkCredVar(State, SR->getSymbol(), Kind);

    if (const SubRegion *ER = dyn_cast<SubRegion>(R))
        return checkCredVar(State, ER->getSuperRegion(), Kind);

    return false;
}


/// Checker registration
void ento::registerCredentialCleanTrackChecker(CheckerManager &Mgr) {
  Mgr.registerChecker<CredentialCleanTrackChecker>();
}

bool ento::shouldRegisterCredentialCleanTrackChecker(const CheckerManager &mgr) {
  return true;
}

