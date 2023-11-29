//=== Taint.h - Taint tracking and basic propagation rules. --------*- C++ -*-//
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

#ifndef LLVM_CLANG_LIB_STATICANALYZER_CHECKERS_TAINT_H
#define LLVM_CLANG_LIB_STATICANALYZER_CHECKERS_TAINT_H

#include "clang/StaticAnalyzer/Core/BugReporter/BugReporterVisitors.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"

namespace clang {
namespace ento {
namespace taint {

/// The type of taint, which helps to differentiate between different types of
/// taint.
using TaintTagType = unsigned;

static constexpr TaintTagType TaintTagGeneric = 0;
static constexpr TaintTagType TaintTagCred = 1;
static constexpr TaintTagType TaintTagRet = 2;
static constexpr TaintTagType TaintTagCredRet = 3;
static constexpr TaintTagType TaintTagNone = 4;
static constexpr TaintTagType TaintTagCredSrcFile = 11;
static constexpr TaintTagType TaintTagCredSrcEnv = 12;
static constexpr TaintTagType TaintTagCredSrcOptarg = 13;
static constexpr TaintTagType TaintTagCredSrcConst = 14;
static constexpr TaintTagType TaintTagCredSrcOtherInput = 15;
static constexpr TaintTagType TaintTagCredUsageCryptoMisuse = 21;
static constexpr TaintTagType TaintTagCredUsageReplay = 22;
// static constexpr TaintTagType TaintTagCredCleanNoMemset = 18;
static constexpr TaintTagType TaintTagCredMemset = 31;
static constexpr TaintTagType TaintTagCredMemsetRet = 32;
static constexpr TaintTagType TaintTagCredFree = 33;
static constexpr TaintTagType TaintTagCredFreeRet = 34;

/// Create a new state in which the value of the statement is marked as tainted.
[[nodiscard]] ProgramStateRef addTaint(ProgramStateRef State, const Stmt *S,
                                       const LocationContext *LCtx,
                                       TaintTagType Kind = TaintTagGeneric);

/// Create a new state in which the value is marked as tainted.
[[nodiscard]] ProgramStateRef addTaint(ProgramStateRef State, SVal V,
                                       TaintTagType Kind = TaintTagGeneric);

/// Create a new state in which the symbol is marked as tainted.
[[nodiscard]] ProgramStateRef addTaint(ProgramStateRef State, SymbolRef Sym,
                                       TaintTagType Kind = TaintTagGeneric);

/// Create a new state in which the pointer represented by the region
/// is marked as tainted.
[[nodiscard]] ProgramStateRef addTaint(ProgramStateRef State,
                                       const MemRegion *R,
                                       TaintTagType Kind = TaintTagGeneric);

[[nodiscard]] ProgramStateRef removeTaint(ProgramStateRef State, SVal V);

[[nodiscard]] ProgramStateRef removeTaint(ProgramStateRef State,
                                          const MemRegion *R);

[[nodiscard]] ProgramStateRef removeTaint(ProgramStateRef State, SymbolRef Sym);

/// Create a new state in a which a sub-region of a given symbol is tainted.
/// This might be necessary when referring to regions that can not have an
/// individual symbol, e.g. if they are represented by the default binding of
/// a LazyCompoundVal.
[[nodiscard]] ProgramStateRef
addPartialTaint(ProgramStateRef State, SymbolRef ParentSym,
                const SubRegion *SubRegion,
                TaintTagType Kind = TaintTagGeneric);

/// Check if the statement has a tainted value in the given state.
bool isTainted(ProgramStateRef State, const Stmt *S,
               const LocationContext *LCtx,
               TaintTagType Kind = TaintTagGeneric);

/// Check if the value is tainted in the given state.
bool isTainted(ProgramStateRef State, SVal V,
               TaintTagType Kind = TaintTagGeneric);

/// Check if the symbol is tainted in the given state.
bool isTainted(ProgramStateRef State, SymbolRef Sym,
               TaintTagType Kind = TaintTagGeneric);

/// Check if the pointer represented by the region is tainted in the given
/// state.
bool isTainted(ProgramStateRef State, const MemRegion *Reg,
               TaintTagType Kind = TaintTagGeneric);

/// Returns the tainted Symbols for a given Statement and state.
std::vector<SymbolRef> getTaintedSymbols(ProgramStateRef State, const Stmt *S,
                                         const LocationContext *LCtx,
                                         TaintTagType Kind = TaintTagGeneric);

/// Returns the tainted Symbols for a given SVal and state.
std::vector<SymbolRef> getTaintedSymbols(ProgramStateRef State, SVal V,
                                         TaintTagType Kind = TaintTagGeneric);

/// Returns the tainted Symbols for a SymbolRef and state.
std::vector<SymbolRef> getTaintedSymbols(ProgramStateRef State, SymbolRef Sym,
                                         TaintTagType Kind = TaintTagGeneric);

/// Returns the tainted (index, super/sub region, symbolic region) symbols
/// for a given memory region.
std::vector<SymbolRef> getTaintedSymbols(ProgramStateRef State,
                                         const MemRegion *Reg,
                                         TaintTagType Kind = TaintTagGeneric);

std::vector<SymbolRef> getTaintedSymbolsImpl(ProgramStateRef State,
                                             const Stmt *S,
                                             const LocationContext *LCtx,
                                             TaintTagType Kind,
                                             bool returnFirstOnly);

std::vector<SymbolRef> getTaintedSymbolsImpl(ProgramStateRef State, SVal V,
                                             TaintTagType Kind,
                                             bool returnFirstOnly);

std::vector<SymbolRef> getTaintedSymbolsImpl(ProgramStateRef State,
                                             SymbolRef Sym, TaintTagType Kind,
                                             bool returnFirstOnly);

std::vector<SymbolRef> getTaintedSymbolsImpl(ProgramStateRef State,
                                             const MemRegion *Reg,
                                             TaintTagType Kind,
                                             bool returnFirstOnly);

void printTaint(ProgramStateRef State, raw_ostream &Out, const char *nl = "\n",
                const char *sep = "");

void removeDupTag(std::vector<TaintTagType> &v);

LLVM_DUMP_METHOD void dumpTaint(ProgramStateRef State);

llvm::ImmutableMap<SymbolRef, llvm::ImmutableSet<TaintTagType>> getSymTaints(ProgramStateRef State);
llvm::ImmutableMap<const ElementRegion *, llvm::ImmutableSet<TaintTagType>> getElementTaints(ProgramStateRef State);

/// The bug visitor prints a diagnostic message at the location where a given
/// variable was tainted.
class TaintBugVisitor final : public BugReporterVisitor {
private:
  const SVal V;

public:
  TaintBugVisitor(const SVal V) : V(V) {}
  void Profile(llvm::FoldingSetNodeID &ID) const override { ID.Add(V); }

  PathDiagnosticPieceRef VisitNode(const ExplodedNode *N,
                                   BugReporterContext &BRC,
                                   PathSensitiveBugReport &BR) override;
};


} // namespace taint
} // namespace ento
} // namespace clang

#endif
