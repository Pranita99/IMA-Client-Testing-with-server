// Path 30: customer_login → try_assign_plumber

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

    // complaint_id = input();
    {
        auto lhs = make_unique<Var>("complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // requesting_customer_id = input();
    {
        auto lhs = make_unique<Var>("requesting_customer_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // preferred_plumber_id = input();
    {
        auto lhs = make_unique<Var>("preferred_plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // service_area = input();
    {
        auto lhs = make_unique<Var>("service_area");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // urgency_level = input();
    {
        auto lhs = make_unique<Var>("urgency_level");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // try_assign_plumber(complaint_id, requesting_customer_id, preferred_plumber_id, service_area, urgency_level);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("requesting_customer_id"));
        a.push_back(make_unique<Var>("preferred_plumber_id"));
        a.push_back(make_unique<Var>("service_area"));
        a.push_back(make_unique<Var>("urgency_level"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("try_assign_plumber", move(a))));
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
        // Check customer is not already logged in
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerLoginStatus", "login_customer_id"));
            eq.push_back(make_unique<Var>("STATUS_LOGGED_OUT"));
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

    // --- try_assign_plumber ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that complaint exists and is pending
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that requesting customer is logged in
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerLoginStatus", "requesting_customer_id"));
            eq.push_back(make_unique<Var>("STATUS_LOGGED_IN"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that requesting customer owns the complaint OR has admin privileges
        {
            vector<unique_ptr<Expr>> ownershipOrAdmin;
            // Option 1: Customer owns the complaint
            {
                vector<unique_ptr<Expr>> ownershipEq;
                ownershipEq.push_back(mapVal("ComplaintCustomers", "complaint_id"));
                ownershipEq.push_back(make_unique<Var>("requesting_customer_id"));
                ownershipOrAdmin.push_back(make_unique<FuncCall>("equals", move(ownershipEq)));
            }
            // Option 2: Customer has admin role (for this example, we'll use ownership only)
            conj.push_back(make_unique<FuncCall>("or_operator", move(ownershipOrAdmin)));
        }
        // Check preferred plumber exists and is available
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("preferred_plumber_id"));
            h.push_back(make_unique<Var>("Plumbers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberStatus", "preferred_plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_AVAILABLE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check plumber serves the requested area
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberServiceAreas", "preferred_plumber_id"));
            eq.push_back(make_unique<Var>("service_area"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("requesting_customer_id"));
        args.push_back(make_unique<Var>("preferred_plumber_id"));
        args.push_back(make_unique<Var>("service_area"));
        args.push_back(make_unique<Var>("urgency_level"));
        auto callFn = make_unique<FuncCall>("try_assign_plumber", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPlumbers", "complaint_id"));
            eq.push_back(make_unique<Var>("preferred_plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_ASSIGNED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberStatus", "preferred_plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_BUSY"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintUrgency", "complaint_id"));
            eq.push_back(make_unique<Var>("urgency_level"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintServiceAreas", "complaint_id"));
            eq.push_back(make_unique<Var>("service_area"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentRequestedBy", "complaint_id"));
            eq.push_back(make_unique<Var>("requesting_customer_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
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

    // Map declarations for complaints
    globals.push_back(make_unique<Decl>("Complaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintCustomers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintPlumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintUrgency", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintServiceAreas", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("AssignmentRequestedBy", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for plumbers
    globals.push_back(make_unique<Decl>("Plumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberServiceAreas", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables for login
    globals.push_back(make_unique<Decl>("login_customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("login_email", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("login_password", make_unique<TypeConst>("string")));

    // Input variables for plumber assignment
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("requesting_customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("preferred_plumber_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("service_area", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("urgency_level", make_unique<TypeConst>("string")));

    // Status constants
    globals.push_back(make_unique<Decl>("STATUS_ACTIVE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_LOGGED_IN", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_LOGGED_OUT", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_PENDING", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ASSIGNED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_AVAILABLE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_BUSY", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("VALID_SESSION", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Customers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerEmails", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerPasswords", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerLoginStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerSessions", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Complaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintCustomers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintPlumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintUrgency", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintServiceAreas", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("AssignmentRequestedBy", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Plumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberServiceAreas", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();