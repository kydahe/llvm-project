//===- PrintFunctionNames.cpp ---------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Example clang plugin which simply prints the names of all the top-level decls
// in the input file.
//
//===----------------------------------------------------------------------===//

#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include "llvm/Support/raw_ostream.h"

#include <utility>
#include<sstream>
#include<iostream>
#include<fstream>

using namespace clang;

std::string func_output_path = "";

namespace {

class PrintFunctionsConsumer : public ASTConsumer {
  CompilerInstance &Instance;
  std::set<std::string> ParsedTemplates;

public:
  PrintFunctionsConsumer(CompilerInstance &Instance,
                         std::set<std::string> ParsedTemplates)
      : Instance(Instance), ParsedTemplates(ParsedTemplates) {}

  bool HandleTopLevelDecl(DeclGroupRef DG) override {
    for (DeclGroupRef::iterator i = DG.begin(), e = DG.end(); i != e; ++i) {
      const Decl *D = *i;
      // if (const NamedDecl *ND = dyn_cast<NamedDecl>(D))
      //   llvm::errs() << "top-level-decl: \"" << ND->getNameAsString() << "\"\n";
      if (const FunctionDecl *FD = dyn_cast<FunctionDecl>(D)){
        std::ostringstream ostring;
        ostring << QualType(FD->getReturnType().getTypePtr()->getUnqualifiedDesugaredType(),0).getAsString();
        ostring << " ";
        ostring << FD->getQualifiedNameAsString();
        ostring << "(";
        // for (ParmVarDecl * pi = FD->param_begin(), pe = FD->param_end(); pi != pe;){
        //     ostring << QualType(pi->getOriginalType().getTypePtr()->getUnqualifiedDesugaredType(), 0).getAsString()
        //     << " " << pi->getNameAsString();
        //     ++pi;
        //     if(pi != pe){
        //       ostring << ", ";
        //     }
        // }
        int n = 0;
        for (auto item : FD->parameters()){
          ostring << QualType(item->getOriginalType().getTypePtr()->getUnqualifiedDesugaredType(), 0).getAsString()
            << " " << item->getNameAsString();
          n++;
          if (n!= FD->param_size()){
            ostring << ", ";
          }
        }
        ostring << ");\n";
        
        std::string result = ostring.str();
        std::ofstream file;
        file.open(func_output_path,std::ios::app);
        file << result;
        file.close();
      }
    }

    return true;
  }

  void HandleTranslationUnit(ASTContext& context) override {
    if (!Instance.getLangOpts().DelayedTemplateParsing)
      return;

    // This demonstrates how to force instantiation of some templates in
    // -fdelayed-template-parsing mode. (Note: Doing this unconditionally for
    // all templates is similar to not using -fdelayed-template-parsig in the
    // first place.)
    // The advantage of doing this in HandleTranslationUnit() is that all
    // codegen (when using -add-plugin) is completely finished and this can't
    // affect the compiler output.
    struct Visitor : public RecursiveASTVisitor<Visitor> {
      const std::set<std::string> &ParsedTemplates;
      Visitor(const std::set<std::string> &ParsedTemplates)
          : ParsedTemplates(ParsedTemplates) {}
      bool VisitFunctionDecl(FunctionDecl *FD) {
        if (FD->isLateTemplateParsed() &&
            ParsedTemplates.count(FD->getNameAsString()))
          LateParsedDecls.insert(FD);
        return true;
      }

      std::set<FunctionDecl*> LateParsedDecls;
    } v(ParsedTemplates);
    v.TraverseDecl(context.getTranslationUnitDecl());
    clang::Sema &sema = Instance.getSema();
    for (const FunctionDecl *FD : v.LateParsedDecls) {
      clang::LateParsedTemplate &LPT =
          *sema.LateParsedTemplateMap.find(FD)->second;
      sema.LateTemplateParser(sema.OpaqueParser, LPT);
      llvm::errs() << "late-parsed-decl: \"" << FD->getNameAsString() << "\"\n";
    } 
  }
};

class PrintFunctionNamesAction : public PluginASTAction {
  std::set<std::string> ParsedTemplates;
protected:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 llvm::StringRef) override {
    return std::make_unique<PrintFunctionsConsumer>(CI, ParsedTemplates);
  }

  bool ParseArgs(const CompilerInstance &CI,
                 const std::vector<std::string> &args) override {
    if(args.size() < 1){
      llvm::errs() << "Lack Output Path!\n";
      return false;
    }
    if(func_output_path == ""){
      func_output_path = args[0];
      // std::ofstream file;
      // file.open(func_output_path, std::ios::out);
      // file.close();
    }
    
    return true;
  }

};

}

static FrontendPluginRegistry::Add<PrintFunctionNamesAction>
X("print-fns", "print function names");
