// Path 3:
// Signup(Customer) → Login → Delete_Account(No_Dues) (Valid path, should return SAT)

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include "../../ast.hpp"
#include "../../symbol_table.hpp"

using namespace std;

// ────────────────────────────────────────────────
// 1. Build the Client Program (imperative path)
// ────────────────────────────────────────────────
static Program buildClientProgram()
{
    vector<unique_ptr<Stmt>> stmts;

    // customer_username = input();
    {
        auto lhs = make_unique<Var>("customer_username");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // customer_password = input();
    {
        auto lhs = make_unique<Var>("customer_password");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // customer_email = input();
    {
        auto lhs = make_unique<Var>("customer_email");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // customer_phone = input();
    {
        auto lhs = make_unique<Var>("customer_phone");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // customer_address = input();
    {
        auto lhs = make_unique<Var>("customer_address");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // signup_customer(customer_username, customer_password, customer_email, customer_phone, customer_address);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customer_username"));
        a.push_back(make_unique<Var>("customer_password"));
        a.push_back(make_unique<Var>("customer_email"));
        a.push_back(make_unique<Var>("customer_phone"));
        a.push_back(make_unique<Var>("customer_address"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_customer", move(a))));
    }

    // login_customer(customer_username, customer_password);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customer_username"));
        a.push_back(make_unique<Var>("customer_password"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("login_customer", move(a))));
    }

    // delete_account(customer_username);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customer_username"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("delete_account", move(a))));
    }

    return Program(std::move(stmts));
}

// ────────────────────────────────────────────────
// 2. Build the API specification
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

    // --- signup_customer ---
    {
        // Precondition: customer_username not in domain of CustomerUsers
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("customer_username"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CustomerUsers"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("not_in", move(preArgs));

        // Function call with customer details
        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("customer_username"));
        args.push_back(make_unique<Var>("customer_password"));
        args.push_back(make_unique<Var>("customer_email"));
        args.push_back(make_unique<Var>("customer_phone"));
        args.push_back(make_unique<Var>("customer_address"));
        auto callFn = make_unique<FuncCall>("signup_customer", move(args));

        // Postcondition: CustomerUsers[customer_username] == customer_profile
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("CustomerUsers", "customer_username"));
        eq.push_back(make_unique<Var>("customer_profile"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- login_customer ---
    {
        vector<unique_ptr<Expr>> conj;

        // CustomerUsers[customer_username] contains customer_password
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerUsers", "customer_username"));
            eq.push_back(make_unique<Var>("customer_password"));
            conj.push_back(make_unique<FuncCall>("contains_password", move(eq)));
        }

        // customer_token not in domain of CustomerSessions
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CustomerSessions"));
            h.push_back(make_unique<Var>("customer_token"));
            conj.push_back(make_unique<FuncCall>("not_in", move(h)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("customer_username"));
        args.push_back(make_unique<Var>("customer_password"));
        auto callFn = make_unique<FuncCall>("login_customer", move(args));

        // Postcondition: CustomerSessions[customer_token] == customer_username
        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("CustomerSessions", "customer_token"));
        eq.push_back(make_unique<Var>("customer_username"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- delete_account ---
    {
        vector<unique_ptr<Expr>> conj;

        // customer_token exists in CustomerSessions (customer is authenticated)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_token"));
            h.push_back(make_unique<Var>("CustomerSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // customer_username exists in CustomerUsers
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_username"));
            h.push_back(make_unique<Var>("CustomerUsers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }

        // CustomerDues[customer_username] == 0 (no pending dues)
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerDues", "customer_username"));
            eq.push_back(make_unique<Var>("ZERO_AMOUNT"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        // No active complaints for this customer
        {
            vector<unique_ptr<Expr>> args;
            args.push_back(make_unique<Var>("customer_username"));
            conj.push_back(make_unique<FuncCall>("no_active_complaints", move(args)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("customer_username"));
        auto callFn = make_unique<FuncCall>("delete_account", move(args));

        vector<unique_ptr<Expr>> postConj;

        // customer_username not in domain of CustomerUsers
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_username"));
            h.push_back(make_unique<Var>("CustomerUsers"));
            postConj.push_back(make_unique<FuncCall>("not_in", move(h)));
        }

        // customer_token not in domain of CustomerSessions
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_token"));
            h.push_back(make_unique<Var>("CustomerSessions"));
            postConj.push_back(make_unique<FuncCall>("not_in", move(h)));
        }

        // CustomerDues[customer_username] is removed
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_username"));
            h.push_back(make_unique<Var>("CustomerDues"));
            postConj.push_back(make_unique<FuncCall>("not_in", move(h)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- Global variable declarations ---
    vector<unique_ptr<Decl>> globals;
    
    // CustomerUsers map: username -> customer profile
    globals.push_back(make_unique<Decl>("CustomerUsers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("CustomerProfile"))));
    
    // CustomerSessions map: token -> username  
    globals.push_back(make_unique<Decl>("CustomerSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // CustomerDues map: username -> amount_owed
    globals.push_back(make_unique<Decl>("CustomerDues", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("number"))));
    
    // CustomerComplaints map: username -> list of complaint_ids
    globals.push_back(make_unique<Decl>("CustomerComplaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("ComplaintList"))));
    
    // Customer session token
    globals.push_back(make_unique<Decl>("customer_token", make_unique<TypeConst>("string")));
    
    // Customer profile containing all customer details
    globals.push_back(make_unique<Decl>("customer_profile", make_unique<TypeConst>("CustomerProfile")));
    
    // Zero amount constant for dues check
    globals.push_back(make_unique<Decl>("ZERO_AMOUNT", make_unique<TypeConst>("number")));

    // --- Initialization ---
    vector<unique_ptr<Init>> inits;
    
    // Initialize CustomerUsers as empty map
    inits.push_back(make_unique<Init>("CustomerUsers", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize CustomerSessions as empty map  
    inits.push_back(make_unique<Init>("CustomerSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize CustomerDues as empty map
    inits.push_back(make_unique<Init>("CustomerDues", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize CustomerComplaints as empty map
    inits.push_back(make_unique<Init>("CustomerComplaints", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();