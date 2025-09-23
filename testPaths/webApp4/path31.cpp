// Path 31: signup(plumber) → login(as_customer)

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

    // plumber_id = input();
    {
        auto lhs = make_unique<Var>("plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_name = input();
    {
        auto lhs = make_unique<Var>("plumber_name");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_email = input();
    {
        auto lhs = make_unique<Var>("plumber_email");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_password = input();
    {
        auto lhs = make_unique<Var>("plumber_password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_phone = input();
    {
        auto lhs = make_unique<Var>("plumber_phone");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // specialization = input();
    {
        auto lhs = make_unique<Var>("specialization");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // signup_plumber(plumber_id, plumber_name, plumber_email, plumber_password, plumber_phone, specialization);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("plumber_id"));
        a.push_back(make_unique<Var>("plumber_name"));
        a.push_back(make_unique<Var>("plumber_email"));
        a.push_back(make_unique<Var>("plumber_password"));
        a.push_back(make_unique<Var>("plumber_phone"));
        a.push_back(make_unique<Var>("specialization"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_plumber", move(a))));
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

    // login_as_customer(login_email, login_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("login_email"));
        a.push_back(make_unique<Var>("login_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_as_customer", move(a))));
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

    // --- signup_plumber ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that plumber doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_id"));
            h.push_back(make_unique<Var>("Plumbers"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check that email is not already registered
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_email"));
            h.push_back(make_unique<Var>("PlumberEmails"));
            auto notInEmail = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notEmailArgs;
            notEmailArgs.push_back(move(notInEmail));
            conj.push_back(make_unique<FuncCall>("not", move(notEmailArgs)));
        }
        // Check that email is also not registered in Customers
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_email"));
            h.push_back(make_unique<Var>("CustomerEmails"));
            auto notInCustomerEmail = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notCustomerEmailArgs;
            notCustomerEmailArgs.push_back(move(notInCustomerEmail));
            conj.push_back(make_unique<FuncCall>("not", move(notCustomerEmailArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("plumber_id"));
        args.push_back(make_unique<Var>("plumber_name"));
        args.push_back(make_unique<Var>("plumber_email"));
        args.push_back(make_unique<Var>("plumber_password"));
        args.push_back(make_unique<Var>("plumber_phone"));
        args.push_back(make_unique<Var>("specialization"));
        auto callFn = make_unique<FuncCall>("signup_plumber", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Plumbers", "plumber_id"));
            eq.push_back(make_unique<Var>("plumber_name"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberEmails", "plumber_email"));
            eq.push_back(make_unique<Var>("plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberPasswords", "plumber_id"));
            eq.push_back(make_unique<Var>("plumber_password"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberPhones", "plumber_id"));
            eq.push_back(make_unique<Var>("plumber_phone"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberSpecializations", "plumber_id"));
            eq.push_back(make_unique<Var>("specialization"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberStatus", "plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- login_as_customer ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that email exists in customers
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("login_email"));
            h.push_back(make_unique<Var>("CustomerEmails"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        // Check password matches for the customer
        {
            vector<unique_ptr<Expr>> eq;
            // First get customer_id from email, then get password from customer_id
            vector<unique_ptr<Expr>> mv1;
            mv1.push_back(make_unique<Var>("CustomerPasswords"));
            vector<unique_ptr<Expr>> mv2;
            mv2.push_back(make_unique<Var>("CustomerEmails"));
            mv2.push_back(make_unique<Var>("login_email"));
            mv1.push_back(make_unique<FuncCall>("mapped_value", move(mv2)));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(mv1)));
            eq.push_back(make_unique<Var>("login_password"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check customer status is active
        {
            vector<unique_ptr<Expr>> eq;
            // First get customer_id from email, then get status from customer_id
            vector<unique_ptr<Expr>> mv1;
            mv1.push_back(make_unique<Var>("CustomerStatus"));
            vector<unique_ptr<Expr>> mv2;
            mv2.push_back(make_unique<Var>("CustomerEmails"));
            mv2.push_back(make_unique<Var>("login_email"));
            mv1.push_back(make_unique<FuncCall>("mapped_value", move(mv2)));
            eq.push_back(make_unique<FuncCall>("mapped_value", move(mv1)));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("login_email"));
        args.push_back(make_unique<Var>("login_password"));
        auto callFn = make_unique<FuncCall>("login_as_customer", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ActiveSessions", "login_email"));
            eq.push_back(make_unique<Var>("SESSION_CUSTOMER"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("LoginAttempts", "login_email"));
            eq.push_back(make_unique<Var>("LOGIN_SUCCESS"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── Globals ───
    vector<unique_ptr<Decl>> globals;

    // Map declarations for plumbers
    globals.push_back(make_unique<Decl>("Plumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberEmails", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberPasswords", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberPhones", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberSpecializations", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for customers
    globals.push_back(make_unique<Decl>("Customers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerEmails", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerPasswords", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for sessions and authentication
    globals.push_back(make_unique<Decl>("ActiveSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("LoginAttempts", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables for plumber signup
    globals.push_back(make_unique<Decl>("plumber_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_name", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_email", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_password", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_phone", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("specialization", make_unique<TypeConst>("string")));

    // Input variables for customer login
    globals.push_back(make_unique<Decl>("login_email", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("login_password", make_unique<TypeConst>("string")));

    // Status and session constants
    globals.push_back(make_unique<Decl>("STATUS_ACTIVE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("SESSION_CUSTOMER", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("LOGIN_SUCCESS", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Plumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberEmails", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberPasswords", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberPhones", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberSpecializations", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Customers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerEmails", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerPasswords", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ActiveSessions", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("LoginAttempts", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();