// Path 33: raise_complaint → assign(plumberX) → plumberY_accept

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

    // complaint_id = input();
    {
        auto lhs = make_unique<Var>("complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // customer_id = input();
    {
        auto lhs = make_unique<Var>("customer_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // complaint_description = input();
    {
        auto lhs = make_unique<Var>("complaint_description");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // service_type = input();
    {
        auto lhs = make_unique<Var>("service_type");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // priority = input();
    {
        auto lhs = make_unique<Var>("priority");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // raise_complaint(complaint_id, customer_id, complaint_description, service_type, priority);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("customer_id"));
        a.push_back(make_unique<Var>("complaint_description"));
        a.push_back(make_unique<Var>("service_type"));
        a.push_back(make_unique<Var>("priority"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("raise_complaint", move(a))));
    }

    // assign_complaint_id = input();
    {
        auto lhs = make_unique<Var>("assign_complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_x_id = input();
    {
        auto lhs = make_unique<Var>("plumber_x_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // assign_plumber(assign_complaint_id, plumber_x_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("assign_complaint_id"));
        a.push_back(make_unique<Var>("plumber_x_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("assign_plumber", move(a))));
    }

    // accept_complaint_id = input();
    {
        auto lhs = make_unique<Var>("accept_complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_y_id = input();
    {
        auto lhs = make_unique<Var>("plumber_y_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_y_accept(accept_complaint_id, plumber_y_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("accept_complaint_id"));
        a.push_back(make_unique<Var>("plumber_y_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_y_accept", move(a))));
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

    // --- raise_complaint ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that complaint doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check customer exists and is active
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_id"));
            h.push_back(make_unique<Var>("Customers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerStatus", "customer_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("customer_id"));
        args.push_back(make_unique<Var>("complaint_description"));
        args.push_back(make_unique<Var>("service_type"));
        args.push_back(make_unique<Var>("priority"));
        auto callFn = make_unique<FuncCall>("raise_complaint", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Complaints", "complaint_id"));
            eq.push_back(make_unique<Var>("complaint_description"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintCustomers", "complaint_id"));
            eq.push_back(make_unique<Var>("customer_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPriority", "complaint_id"));
            eq.push_back(make_unique<Var>("priority"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintServiceType", "complaint_id"));
            eq.push_back(make_unique<Var>("service_type"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- assign_plumber ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check complaint exists and is pending
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("assign_complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "assign_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check plumber X exists and is active
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_x_id"));
            h.push_back(make_unique<Var>("Plumbers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberStatus", "plumber_x_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("assign_complaint_id"));
        args.push_back(make_unique<Var>("plumber_x_id"));
        auto callFn = make_unique<FuncCall>("assign_plumber", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPlumbers", "assign_complaint_id"));
            eq.push_back(make_unique<Var>("plumber_x_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "assign_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_ASSIGNED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- plumber_y_accept (should fail) ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check complaint is assigned (but to different plumber)
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "accept_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_ASSIGNED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check plumber Y exists and is active
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_y_id"));
            h.push_back(make_unique<Var>("Plumbers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberStatus", "plumber_y_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check that complaint is NOT assigned to plumber Y (this should cause failure)
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPlumbers", "accept_complaint_id"));
            eq.push_back(make_unique<Var>("plumber_y_id"));
            auto notEq = make_unique<FuncCall>("equals", move(eq));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notEq));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("accept_complaint_id"));
        args.push_back(make_unique<Var>("plumber_y_id"));
        auto callFn = make_unique<FuncCall>("plumber_y_accept", move(args));

        vector<unique_ptr<Expr>> postConj;
        // This should result in an error state - unauthorized acceptance
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ErrorMessages", "accept_complaint_id"));
            eq.push_back(make_unique<Var>("ERROR_UNAUTHORIZED_ACCEPTANCE"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "accept_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_ASSIGNED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AcceptanceAttempts", "accept_complaint_id"));
            eq.push_back(make_unique<Var>("ACCEPTANCE_UNAUTHORIZED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Complaint should remain assigned to original plumber X
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPlumbers", "accept_complaint_id"));
            eq.push_back(make_unique<Var>("plumber_x_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::BAD_REQUEST_400, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // ─── Globals ───
    vector<unique_ptr<Decl>> globals;

    // Map declarations for complaints
    globals.push_back(make_unique<Decl>("Complaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintCustomers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintPlumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintPriority", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintServiceType", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for customers and plumbers
    globals.push_back(make_unique<Decl>("Customers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("CustomerStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("Plumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for error handling
    globals.push_back(make_unique<Decl>("ErrorMessages", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("AcceptanceAttempts", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables for complaint
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("complaint_description", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("service_type", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("priority", make_unique<TypeConst>("string")));

    // Input variables for assignment
    globals.push_back(make_unique<Decl>("assign_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_x_id", make_unique<TypeConst>("string")));

    // Input variables for acceptance attempt
    globals.push_back(make_unique<Decl>("accept_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_y_id", make_unique<TypeConst>("string")));

    // Status constants
    globals.push_back(make_unique<Decl>("STATUS_PENDING", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ASSIGNED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ACTIVE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("ERROR_UNAUTHORIZED_ACCEPTANCE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("ACCEPTANCE_UNAUTHORIZED", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Complaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintCustomers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintPlumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintPriority", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintServiceType", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Customers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Plumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ErrorMessages", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("AcceptanceAttempts", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();