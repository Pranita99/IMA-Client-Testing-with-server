// Path 26: signup(customer) → signup(same_email)

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

    // customer_id = input();
    {
        auto lhs = make_unique<Var>("customer_id");
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

    // customer_name = input();
    {
        auto lhs = make_unique<Var>("customer_name");
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

    // signup_customer(customer_id, customer_email, customer_name, customer_phone, customer_address);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("customer_id"));
        a.push_back(make_unique<Var>("customer_email"));
        a.push_back(make_unique<Var>("customer_name"));
        a.push_back(make_unique<Var>("customer_phone"));
        a.push_back(make_unique<Var>("customer_address"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_customer", move(a))));
    }

    // duplicate_customer_id = input();
    {
        auto lhs = make_unique<Var>("duplicate_customer_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // duplicate_email = input(); // This will be the same email as customer_email
    {
        auto lhs = make_unique<Var>("duplicate_email");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // duplicate_name = input();
    {
        auto lhs = make_unique<Var>("duplicate_name");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // duplicate_phone = input();
    {
        auto lhs = make_unique<Var>("duplicate_phone");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // duplicate_address = input();
    {
        auto lhs = make_unique<Var>("duplicate_address");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // signup_customer(duplicate_customer_id, duplicate_email, duplicate_name, duplicate_phone, duplicate_address);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("duplicate_customer_id"));
        a.push_back(make_unique<Var>("duplicate_email"));
        a.push_back(make_unique<Var>("duplicate_name"));
        a.push_back(make_unique<Var>("duplicate_phone"));
        a.push_back(make_unique<Var>("duplicate_address"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("signup_customer", move(a))));
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

    // --- signup_customer (first call - should succeed) ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that customer doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_id"));
            h.push_back(make_unique<Var>("Customers"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check that email is not already taken
        {
            vector<unique_ptr<Expr>> emailCheck;
            emailCheck.push_back(make_unique<Var>("customer_email"));
            emailCheck.push_back(make_unique<Var>("CustomerEmails"));
            auto emailNotIn = make_unique<FuncCall>("in", move(emailCheck));
            vector<unique_ptr<Expr>> emailNotArgs;
            emailNotArgs.push_back(move(emailNotIn));
            conj.push_back(make_unique<FuncCall>("not", move(emailNotArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("customer_id"));
        args.push_back(make_unique<Var>("customer_email"));
        args.push_back(make_unique<Var>("customer_name"));
        args.push_back(make_unique<Var>("customer_phone"));
        args.push_back(make_unique<Var>("customer_address"));
        auto callFn = make_unique<FuncCall>("signup_customer", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Customers", "customer_id"));
            eq.push_back(make_unique<Var>("customer_name"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerEmails", "customer_id"));
            eq.push_back(make_unique<Var>("customer_email"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerPhones", "customer_id"));
            eq.push_back(make_unique<Var>("customer_phone"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerAddresses", "customer_id"));
            eq.push_back(make_unique<Var>("customer_address"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerStatus", "customer_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- signup_customer (second call - should fail due to duplicate email) ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that new customer doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("duplicate_customer_id"));
            h.push_back(make_unique<Var>("Customers"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Email already exists (this will make precondition false)
        {
            vector<unique_ptr<Expr>> emailCheck;
            emailCheck.push_back(make_unique<Var>("duplicate_email"));
            emailCheck.push_back(make_unique<Var>("CustomerEmails"));
            auto emailIn = make_unique<FuncCall>("in", move(emailCheck));
            vector<unique_ptr<Expr>> emailNotArgs;
            emailNotArgs.push_back(move(emailIn));
            auto emailNotInCall = make_unique<FuncCall>("not", move(emailNotArgs));
            conj.push_back(move(emailNotInCall));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("duplicate_customer_id"));
        args.push_back(make_unique<Var>("duplicate_email"));
        args.push_back(make_unique<Var>("duplicate_name"));
        args.push_back(make_unique<Var>("duplicate_phone"));
        args.push_back(make_unique<Var>("duplicate_address"));
        auto callFn = make_unique<FuncCall>("signup_customer", move(args));

        // This should fail, so we expect an error response
        vector<unique_ptr<Expr>> errorArgs;
        errorArgs.push_back(make_unique<Var>("error_message"));
        errorArgs.push_back(make_unique<Var>("EMAIL_ALREADY_EXISTS"));
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
    globals.push_back(make_unique<Decl>("CustomerPhones", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerAddresses", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables for first customer
    globals.push_back(make_unique<Decl>("customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_email", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_name", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_phone", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_address", make_unique<TypeConst>("string")));

    // Input variables for duplicate email customer
    globals.push_back(make_unique<Decl>("duplicate_customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("duplicate_email", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("duplicate_name", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("duplicate_phone", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("duplicate_address", make_unique<TypeConst>("string")));

    // Status constants
    globals.push_back(make_unique<Decl>("STATUS_ACTIVE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("EMAIL_ALREADY_EXISTS", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("error_message", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Customers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerEmails", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerPhones", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerAddresses", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();