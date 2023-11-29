//=== Taint.cpp - Taint tracking and basic propagation rules. ------*- C++ -*-//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Defines basic, non-domain-specific mechanisms for tracking tainted values.
//
//===----------------------------------------------------------------------===//

#include "clang/StaticAnalyzer/Checkers/Taint.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include <optional>
#include "Iterator.h"
#include "llvm/ADT/ImmutableMap.h"

using namespace clang;
using namespace ento;
using namespace taint;
using namespace iterator;
using namespace std;
using namespace llvm;


REGISTER_MAP_WITH_PROGRAMSTATE(TaintMap, SymbolRef, TaintTagType)

// Newly added
REGISTER_SET_FACTORY_WITH_PROGRAMSTATE(TaintTagSet, TaintTagType)
REGISTER_MAP_WITH_PROGRAMSTATE(TaintSymMap, SymbolRef, TaintTagSet)

REGISTER_MAP_WITH_PROGRAMSTATE(TaintRegMap, const ElementRegion *, TaintTagSet)

// Partially tainted symbols.
REGISTER_MAP_FACTORY_WITH_PROGRAMSTATE(TaintedSubRegions, const SubRegion *, TaintTagSet)
REGISTER_MAP_WITH_PROGRAMSTATE(DerivedSymTaint, SymbolRef, TaintedSubRegions)

void taint::removeDupTag(std::vector<TaintTagType> &v){
  auto end = v.end();
    for (auto it = v.begin(); it != end; ++it) {
        end = std::remove(it + 1, end, *it);
    }
    v.erase(end, v.end());
}

void taint::printTaint(ProgramStateRef State, raw_ostream &Out, const char *NL,
                       const char *Sep) {
  ImmutableMap<SymbolRef, TaintTagSet> TM = State->get<TaintSymMap>();
  if (!TM.isEmpty())
    Out << "Tainted Symbols:" << NL;

  for(ImmutableMap<SymbolRef, TaintTagSet>::iterator I = TM.begin(), E = TM.end(); I != E; ++I) {
    Out << I->first << " : ";
    for(TaintTagSet::iterator IS = I->second.begin(), ES = I->second.end(); IS != ES; ++ IS)
      Out << (*IS) << ' ';
    Out << NL;
  }

  ImmutableMap<const ElementRegion *, TaintTagSet> TRM = State->get<TaintRegMap>();
  if (!TRM.isEmpty())
    Out << "Tainted Element Region:" << NL;
  
  for(ImmutableMap<const ElementRegion *, TaintTagSet>::iterator I = TRM.begin(), E = TRM.end(); I != E; ++I) {
    Out << I->first << " : ";
    for(TaintTagSet::iterator IS = I->second.begin(), ES = I->second.end(); IS != ES; ++ IS)
      Out << (*IS) << ' ';
    Out << NL;
  }
}

void taint::dumpTaint(ProgramStateRef State) {
  printTaint(State, llvm::dbgs());
}

ProgramStateRef taint::addTaint(ProgramStateRef State, const Stmt *S,
                                const LocationContext *LCtx,
                                TaintTagType Kind) {
  return addTaint(State, State->getSVal(S, LCtx), Kind);
}

ProgramStateRef taint::addTaint(ProgramStateRef State, SVal V,
                                TaintTagType Kind) {
  SymbolRef Sym = V.getAsSymbol();
  if (Sym)
    State = addTaint(State, Sym, Kind);

  if (auto LCV = V.getAs<nonloc::LazyCompoundVal>()) {
    if (std::optional<SVal> binding =
            State->getStateManager().getStoreManager().getDefaultBinding(
                *LCV)) {
      if (SymbolRef Sym = binding->getAsSymbol())
        State = addPartialTaint(State, Sym, LCV->getRegion(), Kind);
    }

    // newly added: structure
    if (auto LCVR = LCV->getRegion()){
      State = addTaint(State, LCVR, Kind);
    }
  }

  if(const MemRegion *R = V.getAsRegion()){
    State = addTaint(State, R, Kind);
  }

  return State;
}

ProgramStateRef taint::addTaint(ProgramStateRef State, const MemRegion *R,
                                TaintTagType Kind) {
  if (!R)
    return State;

  if (const ElementRegion *ER = dyn_cast<ElementRegion>(R)){
    State = addTaint(State, ER->getSuperRegion(), Kind);
    State = addTaint(State, ER->getBaseRegion(), Kind);

    const TaintTagSet *T  = State->get<TaintRegMap>(ER);
    auto &F = State->getStateManager().get_context<TaintTagSet>();
    TaintTagSet Tags = T ? *T : F.getEmptySet();

    Tags = F.add(Tags, Kind);
    State = State->set<TaintRegMap>(ER, Tags);
  }
  if (const SymbolicRegion *SR = dyn_cast_or_null<SymbolicRegion>(R)){
    State = addTaint(State, SR->getSymbol(), Kind);
  }

  if (const SubRegion *ER = dyn_cast<SubRegion>(R)){
    State = addTaint(State, ER->getSuperRegion(), Kind);
  }

  return State;
}

ProgramStateRef taint::addTaint(ProgramStateRef State, SymbolRef Sym,
                                TaintTagType Kind) {
  // If this is a symbol cast, remove the cast before adding the taint. Taint
  // is cast agnostic.
  while (const SymbolCast *SC = dyn_cast<SymbolCast>(Sym))
    Sym = SC->getOperand();
  
  const TaintTagSet *T  = State->get<TaintSymMap>(Sym);
  auto &F = State->getStateManager().get_context<TaintTagSet>();
  TaintTagSet Tags = T ? *T : F.getEmptySet();

  Tags = F.add(Tags, Kind);

  ProgramStateRef NewState = State->set<TaintSymMap>(Sym, Tags);

  assert(NewState);
  return NewState;
}

ProgramStateRef taint::removeTaint(ProgramStateRef State, SVal V) {
  SymbolRef Sym = V.getAsSymbol();
  if (Sym)
    return removeTaint(State, Sym);

  const MemRegion *R = V.getAsRegion();
  return removeTaint(State, R);
}

ProgramStateRef taint::removeTaint(ProgramStateRef State, const MemRegion *R) {
  if (const SymbolicRegion *SR = dyn_cast_or_null<SymbolicRegion>(R))
    State = removeTaint(State, SR->getSymbol());
  if (const ElementRegion *ER = dyn_cast<ElementRegion>(R)){
    State = State->remove<TaintRegMap>(ER);
  }

  return State;
}

ProgramStateRef taint::removeTaint(ProgramStateRef State, SymbolRef Sym) {
  // If this is a symbol cast, remove the cast before adding the taint. Taint
  // is cast agnostic.
  while (const SymbolCast *SC = dyn_cast<SymbolCast>(Sym))
    Sym = SC->getOperand();

  ProgramStateRef NewState = State->remove<TaintSymMap>(Sym);
  assert(NewState);
  return NewState;
}

ProgramStateRef taint::addPartialTaint(ProgramStateRef State,
                                       SymbolRef ParentSym,
                                       const SubRegion *SubRegion,
                                       TaintTagType Kind) {
  // Ignore partial taint if the entire parent symbol is already tainted.
  const TaintTagSet *T = State->get<TaintSymMap>(ParentSym);
  if (T){
    int ret = count(T->begin(), T->end(), Kind);
    if(ret > 0){
      return State;
    }
  }

  if (SubRegion == SubRegion->getBaseRegion())
    return addTaint(State, ParentSym, Kind);

  const TaintedSubRegions *SavedRegs = State->get<DerivedSymTaint>(ParentSym);
  auto &F = State->getStateManager().get_context<TaintedSubRegions>();

  TaintedSubRegions Regs = SavedRegs ? *SavedRegs : F.getEmptyMap();
  auto &TF = State->getStateManager().get_context<TaintTagSet>();
  TaintTagSet Tags = Regs.contains(SubRegion) ? *(Regs.lookup(SubRegion)) : TF.getEmptySet();

  Tags = TF.add(Tags, Kind);
  Regs = F.add(Regs, SubRegion, Tags);

  ProgramStateRef NewState = State->set<DerivedSymTaint>(ParentSym, Regs);
  assert(NewState);
  return NewState;
}

bool taint::isTainted(ProgramStateRef State, const Stmt *S,
                      const LocationContext *LCtx, TaintTagType Kind) {
  SVal val = State->getSVal(S, LCtx);
  return isTainted(State, val, Kind);
}

bool taint::isTainted(ProgramStateRef State, SVal V, TaintTagType Kind) {
  if (SymbolRef Sym = V.getAsSymbol()){
    if (isTainted(State, Sym, Kind) == true){
        return true;
    }
  }

  if (const MemRegion *Reg = V.getAsRegion()){
    if(isTainted(State, Reg, Kind) == true){
        return true;
    }
  }

  if (auto LCV = V.getAs<nonloc::LazyCompoundVal>()) {
    if (std::optional<SVal> binding =
            State->getStateManager().getStoreManager().getDefaultBinding(
                *LCV)) {
      if (SymbolRef Sym = binding->getAsSymbol()){
        if(isTainted(State, Sym, Kind) == true){
            return true;
        }
      }
    }

    if (auto LCVR = LCV->getRegion()){
        if(isTainted(State, LCVR, Kind) == true){
            return true;
        }
    }
    
  }

  return false;
}

bool taint::isTainted(ProgramStateRef State, const MemRegion *Reg,
                      TaintTagType K) {

  if (!Reg)
    return false;
  
  
  if (const ElementRegion *ER = dyn_cast<ElementRegion>(Reg)) {
    const TaintTagSet *T  = State->get<TaintRegMap>(ER);
    if(T){
      int ret = count(T->begin(), T->end(), K);
      if(ret > 0){
        return true;
      }
    }

    return isTainted(State, ER->getSuperRegion(), K) ||
           isTainted(State, ER->getIndex(), K);
  }

  if (const SymbolicRegion *SR = dyn_cast<SymbolicRegion>(Reg)) {
    return isTainted(State, SR->getSymbol(), K);
  }

  if (const SubRegion *ER = dyn_cast<SubRegion>(Reg)) {
    return isTainted(State, ER->getSuperRegion(), K);
  }

  return false;
}

bool taint::isTainted(ProgramStateRef State, SymbolRef Sym, TaintTagType Kind) {
  
  if (!Sym){
    return false;
  }

  for (SymbolRef SubSym : Sym->symbols()) {
    if (!isa<SymbolData>(SubSym))
      continue;
    
    const TaintTagSet *T  = State->get<TaintSymMap>(SubSym);
    if(T){
      int ret = count(T->begin(), T->end(), Kind);
      if(ret > 0){
        return true;
      }
    }

    if (const auto *SD = dyn_cast<SymbolDerived>(SubSym)) {
    
      if (isTainted(State, SD->getParentSymbol(), Kind)){
        return true;
      }

      // If this is a SymbolDerived with the same parent symbol as another
      // tainted SymbolDerived and a region that's a sub-region of that
      // tainted symbol, it's also tainted.
      if (const TaintedSubRegions *Regs =
              State->get<DerivedSymTaint>(SD->getParentSymbol())) {
        const TypedValueRegion *R = SD->getRegion();
        for (auto I : *Regs) {
          const TaintTagSet T  = I.second;
          int ret = count(T.begin(), T.end(), Kind);
          if(ret > 0 && R->isSubRegionOf(I.first)){
            return true;
          }
        }
      }
    }

    // If memory region is tainted, data is also tainted.
    if (const auto *SRV = dyn_cast<SymbolRegionValue>(SubSym)) {
      if (isTainted(State, SRV->getRegion(), Kind)){
        return true;
      }
    }

    // If this is a SymbolCast from a tainted value, it's also tainted.
    if (const auto *SC = dyn_cast<SymbolCast>(SubSym)) {
      if (isTainted(State, SC->getOperand(), Kind)){
        return true;
      }
    }
  }
  return false;
}

std::vector<SymbolRef> taint::getTaintedSymbols(ProgramStateRef State,
                                                const Stmt *S,
                                                const LocationContext *LCtx,
                                                TaintTagType Kind) {
  return getTaintedSymbolsImpl(State, S, LCtx, Kind, /*ReturnFirstOnly=*/false);
}

std::vector<SymbolRef> taint::getTaintedSymbols(ProgramStateRef State, SVal V,
                                                TaintTagType Kind) {
  return getTaintedSymbolsImpl(State, V, Kind, /*ReturnFirstOnly=*/false);
}

std::vector<SymbolRef> taint::getTaintedSymbols(ProgramStateRef State,
                                                SymbolRef Sym,
                                                TaintTagType Kind) {
  return getTaintedSymbolsImpl(State, Sym, Kind, /*ReturnFirstOnly=*/false);
}

std::vector<SymbolRef> taint::getTaintedSymbols(ProgramStateRef State,
                                                const MemRegion *Reg,
                                                TaintTagType Kind) {
  return getTaintedSymbolsImpl(State, Reg, Kind, /*ReturnFirstOnly=*/false);
}

std::vector<SymbolRef> taint::getTaintedSymbolsImpl(ProgramStateRef State,
                                                    const Stmt *S,
                                                    const LocationContext *LCtx,
                                                    TaintTagType Kind,
                                                    bool returnFirstOnly) {
  SVal val = State->getSVal(S, LCtx);
  return getTaintedSymbolsImpl(State, val, Kind, returnFirstOnly);
}

std::vector<SymbolRef> taint::getTaintedSymbolsImpl(ProgramStateRef State,
                                                    SVal V, TaintTagType Kind,
                                                    bool returnFirstOnly) {
  if (SymbolRef Sym = V.getAsSymbol())
    return getTaintedSymbolsImpl(State, Sym, Kind, returnFirstOnly);
  if (const MemRegion *Reg = V.getAsRegion())
    return getTaintedSymbolsImpl(State, Reg, Kind, returnFirstOnly);
  return {};
}

std::vector<SymbolRef> taint::getTaintedSymbolsImpl(ProgramStateRef State,
                                                    const MemRegion *Reg,
                                                    TaintTagType K,
                                                    bool returnFirstOnly) {
  std::vector<SymbolRef> TaintedSymbols;
  if (!Reg)
    return TaintedSymbols;
  // Element region (array element) is tainted if either the base or the offset
  // are tainted.
  if (const ElementRegion *ER = dyn_cast<ElementRegion>(Reg)) {
    std::vector<SymbolRef> TaintedIndex =
        getTaintedSymbolsImpl(State, ER->getIndex(), K, returnFirstOnly);
    llvm::append_range(TaintedSymbols, TaintedIndex);
    if (returnFirstOnly && !TaintedSymbols.empty())
      return TaintedSymbols; // return early if needed
    std::vector<SymbolRef> TaintedSuperRegion =
        getTaintedSymbolsImpl(State, ER->getSuperRegion(), K, returnFirstOnly);
    llvm::append_range(TaintedSymbols, TaintedSuperRegion);
    if (returnFirstOnly && !TaintedSymbols.empty())
      return TaintedSymbols; // return early if needed
  }

  if (const SymbolicRegion *SR = dyn_cast<SymbolicRegion>(Reg)) {
    std::vector<SymbolRef> TaintedRegions =
        getTaintedSymbolsImpl(State, SR->getSymbol(), K, returnFirstOnly);
    llvm::append_range(TaintedSymbols, TaintedRegions);
    if (returnFirstOnly && !TaintedSymbols.empty())
      return TaintedSymbols; // return early if needed
  }

  if (const SubRegion *ER = dyn_cast<SubRegion>(Reg)) {
    std::vector<SymbolRef> TaintedSubRegions =
        getTaintedSymbolsImpl(State, ER->getSuperRegion(), K, returnFirstOnly);
    llvm::append_range(TaintedSymbols, TaintedSubRegions);
    if (returnFirstOnly && !TaintedSymbols.empty())
      return TaintedSymbols; // return early if needed
  }

  return TaintedSymbols;
}

std::vector<SymbolRef> taint::getTaintedSymbolsImpl(ProgramStateRef State,
                                                    SymbolRef Sym,
                                                    TaintTagType Kind,
                                                    bool returnFirstOnly) {
  std::vector<SymbolRef> TaintedSymbols;
  if (!Sym)
    return TaintedSymbols;

  // Traverse all the symbols this symbol depends on to see if any are tainted.
  for (SymbolRef SubSym : Sym->symbols()) {
    if (!isa<SymbolData>(SubSym))
      continue;

    if (const TaintTagType *Tag = State->get<TaintMap>(SubSym)) {
      if (*Tag == Kind) {
        TaintedSymbols.push_back(SubSym);
        if (returnFirstOnly)
          return TaintedSymbols; // return early if needed
      }
    }

    if (const auto *SD = dyn_cast<SymbolDerived>(SubSym)) {
      // If this is a SymbolDerived with a tainted parent, it's also tainted.
      std::vector<SymbolRef> TaintedParents = getTaintedSymbolsImpl(
          State, SD->getParentSymbol(), Kind, returnFirstOnly);
      llvm::append_range(TaintedSymbols, TaintedParents);
      if (returnFirstOnly && !TaintedSymbols.empty())
        return TaintedSymbols; // return early if needed

      // If this is a SymbolDerived with the same parent symbol as another
      // tainted SymbolDerived and a region that's a sub-region of that
      // tainted symbol, it's also tainted.
      if (const TaintedSubRegions *Regs =
              State->get<DerivedSymTaint>(SD->getParentSymbol())) {
        const TypedValueRegion *R = SD->getRegion();
        for (auto I : *Regs) {
          // FIXME: The logic to identify tainted regions could be more
          // complete. For example, this would not currently identify
          // overlapping fields in a union as tainted. To identify this we can
          // check for overlapping/nested byte offsets.
          const TaintTagSet T  = I.second;
          int ret = count(T.begin(), T.end(), Kind);
          if (ret > 0 && R->isSubRegionOf(I.first)) {
            TaintedSymbols.push_back(SD->getParentSymbol());
            if (returnFirstOnly && !TaintedSymbols.empty())
              return TaintedSymbols; // return early if needed
          }
        }
      }
    }

    // If memory region is tainted, data is also tainted.
    if (const auto *SRV = dyn_cast<SymbolRegionValue>(SubSym)) {
      std::vector<SymbolRef> TaintedRegions =
          getTaintedSymbolsImpl(State, SRV->getRegion(), Kind, returnFirstOnly);
      llvm::append_range(TaintedSymbols, TaintedRegions);
      if (returnFirstOnly && !TaintedSymbols.empty())
        return TaintedSymbols; // return early if needed
    }

    // If this is a SymbolCast from a tainted value, it's also tainted.
    if (const auto *SC = dyn_cast<SymbolCast>(SubSym)) {
      std::vector<SymbolRef> TaintedCasts =
          getTaintedSymbolsImpl(State, SC->getOperand(), Kind, returnFirstOnly);
      llvm::append_range(TaintedSymbols, TaintedCasts);
      if (returnFirstOnly && !TaintedSymbols.empty())
        return TaintedSymbols; // return early if needed
    }
  }
  return TaintedSymbols;
}


PathDiagnosticPieceRef TaintBugVisitor::VisitNode(const ExplodedNode *N,
                                                  BugReporterContext &BRC,
                                                  PathSensitiveBugReport &BR) {

  // Find the ExplodedNode where the taint was first introduced
  if (!isTainted(N->getState(), V) ||
      isTainted(N->getFirstPred()->getState(), V))
    return nullptr;

  const Stmt *S = N->getStmtForDiagnostics();
  if (!S)
    return nullptr;

  const LocationContext *NCtx = N->getLocationContext();
  PathDiagnosticLocation L =
      PathDiagnosticLocation::createBegin(S, BRC.getSourceManager(), NCtx);
  if (!L.isValid() || !L.asLocation().isValid())
    return nullptr;

  return std::make_shared<PathDiagnosticEventPiece>(L, "Taint originated here");
}