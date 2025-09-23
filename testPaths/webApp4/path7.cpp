// Path 7:
// Raise_Complaint → Assign(Plumber) → Plumber_Accept → Under_Examination → Quotation → Customer_Accept → Execution → Incomplete → Cancelled (Valid path, should return SAT)

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

    // complaint_description = input();
    {
        auto lhs = make_unique<Var>("complaint_description");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // customer_location = input();
    {
        auto lhs = make_unique<Var>("customer_location");
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

    // raise_complaint(complaint_description, customer_location, service_type);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_description"));
        a.push_back(make_unique<Var>("customer_location"));
        a.push_back(make_unique<Var>("service_type"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("raise_complaint", move(a))));
    }

    // plumber_id = input();
    {
        auto lhs = make_unique<Var>("plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // assign_plumber(complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("assign_plumber", move(a))));
    }

    // plumber_accept(complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_accept", move(a))));
    }

    // start_examination(complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("start_examination", move(a))));
    }

    // estimated_cost = input();
    {
        auto lhs = make_unique<Var>("estimated_cost");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // spare_parts_needed = input();
    {
        auto lhs = make_unique<Var>("spare_parts_needed");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // raise_quotation(complaint_id, estimated_cost, spare_parts_needed);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("estimated_cost"));
        a.push_back(make_unique<Var>("spare_parts_needed"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("raise_quotation", move(a))));
    }

    // customer_accept_quotation(complaint_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("customer_accept_quotation", move(a))));
    }

    // start_execution(complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("start_execution", move(a))));
    }

    // incomplete_reason = input();
    {
        auto lhs = make_unique<Var>("incomplete_reason");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
                         make_unique<FuncCall>("input", move(a))));
    }

    // mark_incomplete(complaint_id, incomplete_reason);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("incomplete_reason"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("mark_incomplete", move(a))));
    }

    // cancel_complaint(complaint_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("cancel_complaint", move(a))));
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

    // --- raise_complaint ---
    {
        vector<unique_ptr<Expr>> preArgs;
        preArgs.push_back(make_unique<Var>("customer_token"));
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("CustomerSessions"));
            preArgs.push_back(make_unique<FuncCall>("dom", move(h)));
        }
        auto pre = make_unique<FuncCall>("in", move(preArgs));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_description"));
        args.push_back(make_unique<Var>("customer_location"));
        args.push_back(make_unique<Var>("service_type"));
        auto callFn = make_unique<FuncCall>("raise_complaint", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_RAISED"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::CREATED_201, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- assign_plumber ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("manager_token"));
            h.push_back(make_unique<Var>("ManagerSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_RAISED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("assign_plumber", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_ASSIGNED"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- plumber_accept ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_token"));
            h.push_back(make_unique<Var>("PlumberSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_ASSIGNED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("plumber_accept", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_ACCEPTED"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- start_examination ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_token"));
            h.push_back(make_unique<Var>("PlumberSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_ACCEPTED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("start_examination", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_UNDER_EXAMINATION"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- raise_quotation ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_token"));
            h.push_back(make_unique<Var>("PlumberSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_UNDER_EXAMINATION"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("estimated_cost"));
        args.push_back(make_unique<Var>("spare_parts_needed"));
        auto callFn = make_unique<FuncCall>("raise_quotation", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_QUOTATION_RAISED"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- customer_accept_quotation ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_token"));
            h.push_back(make_unique<Var>("CustomerSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_QUOTATION_RAISED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        auto callFn = make_unique<FuncCall>("customer_accept_quotation", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_UNDER_EXECUTION"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- start_execution ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_token"));
            h.push_back(make_unique<Var>("PlumberSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_UNDER_EXECUTION"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("start_execution", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ExecutionStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("EXECUTION_STARTED"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- mark_incomplete ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_token"));
            h.push_back(make_unique<Var>("PlumberSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("STATE_UNDER_EXECUTION"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("incomplete_reason"));
        auto callFn = make_unique<FuncCall>("mark_incomplete", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ExecutionStatus", "complaint_id"));
            eq.push_back(make_unique<Var>("EXECUTION_INCOMPLETE"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("IncompleteReasons", "complaint_id"));
            eq.push_back(make_unique<Var>("incomplete_reason"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }

        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- cancel_complaint ---
    {
        vector<unique_ptr<Expr>> conj;
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("customer_token"));
            h.push_back(make_unique<Var>("CustomerSessions"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> args;
            args.push_back(make_unique<Var>("complaint_id"));
            conj.push_back(make_unique<FuncCall>("execution_incomplete", move(args)));
        }

        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        auto callFn = make_unique<FuncCall>("cancel_complaint", move(args));

        vector<unique_ptr<Expr>> eq;
        eq.push_back(mapVal("ComplaintStatus", "complaint_id"));
        eq.push_back(make_unique<Var>("STATE_CANCELLED"));
        auto post = make_unique<FuncCall>("equals", move(eq));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- Global variable declarations ---
    vector<unique_ptr<Decl>> globals;
    
    // User session maps
    globals.push_back(make_unique<Decl>("CustomerSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ManagerSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberSessions", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // Complaint tracking maps
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintAssignments", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintQuotations", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("QuotationDetails"))));
    
    // Execution tracking
    globals.push_back(make_unique<Decl>("ExecutionStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("IncompleteReasons", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    
    // Session tokens
    globals.push_back(make_unique<Decl>("customer_token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("manager_token", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_token", make_unique<TypeConst>("string")));
    
    // Complaint ID
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    
    // Complaint state constants
    globals.push_back(make_unique<Decl>("STATE_RAISED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_ASSIGNED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_ACCEPTED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_UNDER_EXAMINATION", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_QUOTATION_RAISED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_UNDER_EXECUTION", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATE_CANCELLED", make_unique<TypeConst>("string")));
    
    // Execution status constants
    globals.push_back(make_unique<Decl>("EXECUTION_STARTED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("EXECUTION_INCOMPLETE", make_unique<TypeConst>("string")));

    // --- Initialization ---
    vector<unique_ptr<Init>> inits;
    
    // Initialize all session maps as empty
    inits.push_back(make_unique<Init>("CustomerSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("ManagerSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("PlumberSessions", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    
    // Initialize complaint tracking maps as empty
    inits.push_back(make_unique<Init>("ComplaintStatus", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("ComplaintAssignments", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("ComplaintQuotations", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("ExecutionStatus", 
        make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>())));
    inits.push_back(make_unique<Init>("IncompleteReasons", 
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