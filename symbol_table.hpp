#pragma once
#include <vector>
#include <set>
#include <map>
#include <string>
#include <memory>
#include "ast.hpp"     


class SymbolTable {
public:
    std::vector<SymbolTable*> children;
    SymbolTable*              par = nullptr;
    std::set<Var>             symtable;

    bool exists(const Var& v) const {
        return symtable.find(v) != symtable.end();
    }
    std::string to_string() const {
        std::string s;
        for (const auto& var : symtable) s += var.name + " ";
        return s;
    }
};


class TypeMap {
public:
    TypeMap*                     par      = nullptr;
    std::vector<TypeMap*>        children;
    std::map<std::string, TypeExpr*> mapping;

    
    auto begin()               { return mapping.begin(); }
    auto end()                 { return mapping.end();   }
    auto begin() const         { return mapping.begin(); }
    auto end()   const         { return mapping.end();   }
};
