#pragma once
#include <vector>
#include <set>
#include <map>
#include <string>
#include <memory>
#include "ast.hpp"  // This provides the Var declaration

class SymbolTable {
public:
    std::vector<SymbolTable*> children;
    SymbolTable* par;
    std::set<Var> symtable;
    
    bool exists(const Var& v) {
        return symtable.find(v) != symtable.end();
    }

    std::string to_string() {
        std::string s;
        for (const auto& var : symtable) {
            s += var.name + " ";
        }
        return s;
    }
};

class TypeMap {
public:
    TypeMap* par;
    std::vector<TypeMap*> children;
    std::map<std::string, TypeExpr*> mapping;
};