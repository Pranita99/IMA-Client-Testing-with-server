// Path 19: Signup(Manager) → Login

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ────────────────────────────────────────────────
// 1. Build the Client Program
// ────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // manager_username = input();
    {
        auto lhs = make_unique<Var>("manager_username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // manager_password = input();
    {
        auto lhs = make_unique<Var>("manager_password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // manager_email = input();
    {
        auto lhs = make_unique<Var>("manager_email");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // manager_id = input();
    {
        auto lhs = make_unique<Var>("manager_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // signup_manager(manager_username, manager_password, manager_email, manager_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("manager_username"));
        a.push_back(make_unique<Var>("manager_password"));
        a.push_back(make_unique<Var>("manager_email"));
        a.push_back(make_unique<Var>("manager_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_manager", move(a))));
    }

    // login_username = input();
    {
        auto lhs = make_unique<Var>("login_username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // login_password = input();
    {
        auto lhs = make_unique<Var>("login_password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // manager_login(login_username, login_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("login_username"));
        a.push_back(make_unique<Var>("login_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("manager_login", move(a))));
    }

    return Program(std::move(stmts));
}

// ────────────────────────────────────────────────
// 2. Build the API Specification
// ────────────────────────────────────────────────
static Spec buildSpec()
{
    auto mapVal = [](const string& map, const string& key){
        vector<unique_ptr<Expr>> mv;
        mv.push_back(make_unique<Var>(map));
        mv.push_back(make_unique<Var>(key));
        return make_unique<FuncCall>("mapped_value", move(mv));
    };

    vector<unique_ptr<API>> blocks;

    // --- signup_manager ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that username doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("manager_username"));
            h.push_back(make_unique<Var>("ManagerCredentials"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("manager_username"));
        args.push_back(make_unique<Var>("manager_password"));
        args.push_back(make_unique<Var>("manager_email"));
        args.push_back(make_unique<Var>("manager_id"));
        auto callFn = make_unique<FuncCall>("signup_manager", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ManagerCredentials", "manager_username"));
            eq.push_back(make_unique<Var>("manager_password"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ManagerDetails", "manager_username"));
            eq.push_back(make_unique<Var>("manager_email"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ManagerIDs", "manager_username"));
            eq.push_back(make_unique<Var>("manager_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ManagerStatus", "manager_username"));
            eq.push_back(make_unique<Var>("STATUS_REGISTERED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- manager_login ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ManagerCredentials", "login_username"));
            eq.push_back(make_unique<Var>("login_password"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ManagerStatus", "login_username"));
            eq.push_back(make_unique<Var>("STATUS_REGISTERED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("login_username"));
        args.push_back(make_unique<Var>("login_password"));
        auto callFn = make_unique<FuncCall>("manager_login", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ManagerLoginStatus", "login_username"));
            eq.push_back(make_unique<Var>("STATUS_LOGGED_IN"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── Globals ───
    vector<unique_ptr<Decl>> globals;

    // Map declarations for manager management
    globals.push_back(make_unique<Decl>("ManagerCredentials", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ManagerDetails", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ManagerIDs", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ManagerStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ManagerLoginStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables
    globals.push_back(make_unique<Decl>("manager_username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("manager_password", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("manager_email", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("manager_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("login_username", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("login_password", make_unique<TypeConst>("string")));

    // Status constants
    globals.push_back(make_unique<Decl>("STATUS_REGISTERED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_LOGGED_IN", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("ManagerCredentials", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ManagerDetails", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ManagerIDs", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ManagerStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ManagerLoginStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();