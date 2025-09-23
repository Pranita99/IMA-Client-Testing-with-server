// Path 27: login(customer) → delete_account(with_dues)

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

    // login_customer_id = input();
    {
        auto lhs = make_unique<Var>("login_customer_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // login_email = input();
    {
        auto lhs = make_unique<Var>("login_email");
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

    // customer_login(login_customer_id, login_email, login_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("login_customer_id"));
        a.push_back(make_unique<Var>("login_email"));
        a.push_back(make_unique<Var>("login_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("customer_login", move(a))));
    }

    // delete_customer_id = input();
    {
        auto lhs = make_unique<Var>("delete_customer_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // delete_password = input();
    {
        auto lhs = make_unique<Var>("delete_password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // delete_account(delete_customer_id, delete_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("delete_customer_id"));
        a.push_back(make_unique<Var>("delete_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("delete_account", move(a))));
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

    // --- customer_login ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that customer exists
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("login_customer_id"));
            h.push_back(make_unique<Var>("Customers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        // Check that customer is active
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerStatus", "login_customer_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check email matches
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerEmails", "login_customer_id"));
            eq.push_back(make_unique<Var>("login_email"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check password matches
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerPasswords", "login_customer_id"));
            eq.push_back(make_unique<Var>("login_password"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("login_customer_id"));
        args.push_back(make_unique<Var>("login_email"));
        args.push_back(make_unique<Var>("login_password"));
        auto callFn = make_unique<FuncCall>("customer_login", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerLoginStatus", "login_customer_id"));
            eq.push_back(make_unique<Var>("STATUS_LOGGED_IN"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerSessions", "login_customer_id"));
            eq.push_back(make_unique<Var>("VALID_SESSION"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- delete_account (should fail due to outstanding dues) ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that customer exists
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("delete_customer_id"));
            h.push_back(make_unique<Var>("Customers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        // Check that customer is logged in
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerLoginStatus", "delete_customer_id"));
            eq.push_back(make_unique<Var>("STATUS_LOGGED_IN"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check password matches
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerPasswords", "delete_customer_id"));
            eq.push_back(make_unique<Var>("delete_password"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that customer has NO outstanding dues (this will be false, causing failure)
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerOutstandingDues", "delete_customer_id"));
            eq.push_back(make_unique<Var>("NO_DUES"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("delete_customer_id"));
        args.push_back(make_unique<Var>("delete_password"));
        auto callFn = make_unique<FuncCall>("delete_account", move(args));

        // This should fail due to outstanding dues
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("error_message"));
        errorArgs.push_back(make_unique<Var>("CANNOT_DELETE_ACCOUNT_WITH_DUES"));
        auto errorPost = make_unique<FuncCall>("equals", move(errorArgs));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, errorPost->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── Globals ───
    vector<unique_ptr<Decl>> globals;

    // Map declarations for customers
    globals.push_back(make_unique<Decl>("Customers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerEmails", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerPasswords", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerLoginStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerOutstandingDues", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables for login
    globals.push_back(make_unique<Decl>("login_customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("login_email", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("login_password", make_unique<TypeConst>("string")));

    // Input variables for delete account
    globals.push_back(make_unique<Decl>("delete_customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("delete_password", make_unique<TypeConst>("string")));

    // Status constants
    globals.push_back(make_unique<Decl>("STATUS_ACTIVE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_LOGGED_IN", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_DELETED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("VALID_SESSION", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("NO_DUES", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("CANNOT_DELETE_ACCOUNT_WITH_DUES", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("error_message", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Customers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerEmails", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerPasswords", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerLoginStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerSessions", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerOutstandingDues", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();