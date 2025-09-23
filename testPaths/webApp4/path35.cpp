// Path 35: raise_complaint(repair) → assign(plumber) → plumber_accept → quotation(spare_not_in_catalog) → charge_customer

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

    // complaint_customer_id = input();
    {
        auto lhs = make_unique<Var>("complaint_customer_id");
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

    // raise_repair_complaint(complaint_id, complaint_customer_id, complaint_description, service_type, priority);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("complaint_id"));
        a.push_back(make_unique<Var>("complaint_customer_id"));
        a.push_back(make_unique<Var>("complaint_description"));
        a.push_back(make_unique<Var>("service_type"));
        a.push_back(make_unique<Var>("priority"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("raise_repair_complaint", move(a))));
    }

    // assignment_id = input();
    {
        auto lhs = make_unique<Var>("assignment_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // assignment_complaint_id = input();
    {
        auto lhs = make_unique<Var>("assignment_complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_id = input();
    {
        auto lhs = make_unique<Var>("plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // assign_plumber(assignment_id, assignment_complaint_id, plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("assignment_id"));
        a.push_back(make_unique<Var>("assignment_complaint_id"));
        a.push_back(make_unique<Var>("plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("assign_plumber", move(a))));
    }

    // acceptance_assignment_id = input();
    {
        auto lhs = make_unique<Var>("acceptance_assignment_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // accepting_plumber_id = input();
    {
        auto lhs = make_unique<Var>("accepting_plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // plumber_accept_assignment(acceptance_assignment_id, accepting_plumber_id);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("acceptance_assignment_id"));
        a.push_back(make_unique<Var>("accepting_plumber_id"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("plumber_accept_assignment", move(a))));
    }

    // quotation_id = input();
    {
        auto lhs = make_unique<Var>("quotation_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // quotation_complaint_id = input();
    {
        auto lhs = make_unique<Var>("quotation_complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // quotation_plumber_id = input();
    {
        auto lhs = make_unique<Var>("quotation_plumber_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // spare_id = input();
    {
        auto lhs = make_unique<Var>("spare_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // quotation_amount = input();
    {
        auto lhs = make_unique<Var>("quotation_amount");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // create_quotation_with_spare(quotation_id, quotation_complaint_id, quotation_plumber_id, spare_id, quotation_amount);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("quotation_id"));
        a.push_back(make_unique<Var>("quotation_complaint_id"));
        a.push_back(make_unique<Var>("quotation_plumber_id"));
        a.push_back(make_unique<Var>("spare_id"));
        a.push_back(make_unique<Var>("quotation_amount"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("create_quotation_with_spare", move(a))));
    }

    // charge_id = input();
    {
        auto lhs = make_unique<Var>("charge_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // charge_customer_id = input();
    {
        auto lhs = make_unique<Var>("charge_customer_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // charge_complaint_id = input();
    {
        auto lhs = make_unique<Var>("charge_complaint_id");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // charge_amount = input();
    {
        auto lhs = make_unique<Var>("charge_amount");
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>(""));
        stmts.push_back(make_unique<Assign>(move(lhs),
            make_unique<FuncCall>("input", move(a))));
    }

    // charge_customer(charge_id, charge_customer_id, charge_complaint_id, charge_amount);
    {
        vector<unique_ptr<Expr>> a;
        a.push_back(make_unique<Var>("charge_id"));
        a.push_back(make_unique<Var>("charge_customer_id"));
        a.push_back(make_unique<Var>("charge_complaint_id"));
        a.push_back(make_unique<Var>("charge_amount"));
        stmts.push_back(make_unique<FuncCallStmt>(
            make_unique<FuncCall>("charge_customer", move(a))));
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

    // --- raise_repair_complaint ---
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
            h.push_back(make_unique<Var>("complaint_customer_id"));
            h.push_back(make_unique<Var>("Customers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerStatus", "complaint_customer_id"));
            eq.push_back(make_unique<Var>("STATUS_ACTIVE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check service type is repair
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(make_unique<Var>("service_type"));
            eq.push_back(make_unique<Var>("SERVICE_TYPE_REPAIR"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("complaint_id"));
        args.push_back(make_unique<Var>("complaint_customer_id"));
        args.push_back(make_unique<Var>("complaint_description"));
        args.push_back(make_unique<Var>("service_type"));
        args.push_back(make_unique<Var>("priority"));
        auto callFn = make_unique<FuncCall>("raise_repair_complaint", move(args));

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
            eq.push_back(make_unique<Var>("complaint_customer_id"));
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
            eq.push_back(mapVal("ComplaintServiceType", "complaint_id"));
            eq.push_back(make_unique<Var>("SERVICE_TYPE_REPAIR"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintPriority", "complaint_id"));
            eq.push_back(make_unique<Var>("priority"));
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
        // Check that assignment doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("assignment_id"));
            h.push_back(make_unique<Var>("Assignments"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check complaint exists and is pending
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("assignment_complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "assignment_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check plumber exists and is available
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("plumber_id"));
            h.push_back(make_unique<Var>("Plumbers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberStatus", "plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_AVAILABLE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("assignment_id"));
        args.push_back(make_unique<Var>("assignment_complaint_id"));
        args.push_back(make_unique<Var>("plumber_id"));
        auto callFn = make_unique<FuncCall>("assign_plumber", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Assignments", "assignment_id"));
            eq.push_back(make_unique<Var>("assignment_complaint_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentPlumbers", "assignment_id"));
            eq.push_back(make_unique<Var>("plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentStatus", "assignment_id"));
            eq.push_back(make_unique<Var>("STATUS_ASSIGNED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "assignment_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_ASSIGNED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- plumber_accept_assignment ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check assignment exists and is assigned
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("acceptance_assignment_id"));
            h.push_back(make_unique<Var>("Assignments"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentStatus", "acceptance_assignment_id"));
            eq.push_back(make_unique<Var>("STATUS_ASSIGNED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check plumber matches assignment
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentPlumbers", "acceptance_assignment_id"));
            eq.push_back(make_unique<Var>("accepting_plumber_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check plumber is still available
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberStatus", "accepting_plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_AVAILABLE"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("acceptance_assignment_id"));
        args.push_back(make_unique<Var>("accepting_plumber_id"));
        auto callFn = make_unique<FuncCall>("plumber_accept_assignment", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("AssignmentStatus", "acceptance_assignment_id"));
            eq.push_back(make_unique<Var>("STATUS_ACCEPTED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberStatus", "accepting_plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_BUSY"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Update related complaint status to in progress
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "quotation_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_IN_PROGRESS"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- create_quotation_with_spare (spare not in catalog) ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that quotation doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("quotation_id"));
            h.push_back(make_unique<Var>("Quotations"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check complaint exists and is in progress
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("quotation_complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "quotation_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_IN_PROGRESS"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check plumber exists and is busy
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("quotation_plumber_id"));
            h.push_back(make_unique<Var>("Plumbers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("PlumberStatus", "quotation_plumber_id"));
            eq.push_back(make_unique<Var>("STATUS_BUSY"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check spare is NOT in catalog (key constraint)
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("spare_id"));
            h.push_back(make_unique<Var>("SpareCatalog"));
            auto notInSpare = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notSpareArgs;
            notSpareArgs.push_back(move(notInSpare));
            conj.push_back(make_unique<FuncCall>("not", move(notSpareArgs)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("quotation_id"));
        args.push_back(make_unique<Var>("quotation_complaint_id"));
        args.push_back(make_unique<Var>("quotation_plumber_id"));
        args.push_back(make_unique<Var>("spare_id"));
        args.push_back(make_unique<Var>("quotation_amount"));
        auto callFn = make_unique<FuncCall>("create_quotation_with_spare", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("Quotations", "quotation_id"));
            eq.push_back(make_unique<Var>("quotation_amount"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationComplaints", "quotation_complaint_id"));
            eq.push_back(make_unique<Var>("quotation_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationPlumbers", "quotation_id"));
            eq.push_back(make_unique<Var>("quotation_plumber_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationSpares", "quotation_id"));
            eq.push_back(make_unique<Var>("spare_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("QuotationStatus", "quotation_id"));
            eq.push_back(make_unique<Var>("STATUS_PENDING_APPROVAL"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Mark spare as non-catalog item
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("SpareAvailability", "spare_id"));
            eq.push_back(make_unique<Var>("SPARE_NOT_IN_CATALOG"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "quotation_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_QUOTED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto post = make_unique<FuncCall>("and_operator", move(postConj));

        Response resp(HTTPResponseCode::OK_200, post->clone());
        auto apicall = make_unique<APIcall>(std::move(callFn), std::move(resp));
        blocks.push_back(make_unique<API>(move(pre), move(apicall), move(resp)));
    }

    // --- charge_customer ---
    {
        vector<unique_ptr<Expr>> conj;
        // Check that charge doesn't already exist
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("charge_id"));
            h.push_back(make_unique<Var>("CustomerCharges"));
            auto notIn = make_unique<FuncCall>("in", move(h));
            vector<unique_ptr<Expr>> notArgs;
            notArgs.push_back(move(notIn));
            conj.push_back(make_unique<FuncCall>("not", move(notArgs)));
        }
        // Check customer exists
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("charge_customer_id"));
            h.push_back(make_unique<Var>("Customers"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        // Check complaint exists and is quoted
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("charge_complaint_id"));
            h.push_back(make_unique<Var>("Complaints"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "charge_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_QUOTED"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check customer matches complaint
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintCustomers", "charge_complaint_id"));
            eq.push_back(make_unique<Var>("charge_customer_id"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        // Check quotation exists for complaint
        {
            vector<unique_ptr<Expr>> h;
            h.push_back(make_unique<Var>("charge_complaint_id"));
            h.push_back(make_unique<Var>("QuotationComplaints"));
            conj.push_back(make_unique<FuncCall>("in", move(h)));
        }
        // Check charge amount matches quotation amount
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(make_unique<Var>("charge_amount"));
            eq.push_back(make_unique<Var>("quotation_amount"));
            conj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        auto pre = make_unique<FuncCall>("and_operator", move(conj));

        vector<unique_ptr<Expr>> args;
        args.push_back(make_unique<Var>("charge_id"));
        args.push_back(make_unique<Var>("charge_customer_id"));
        args.push_back(make_unique<Var>("charge_complaint_id"));
        args.push_back(make_unique<Var>("charge_amount"));
        auto callFn = make_unique<FuncCall>("charge_customer", move(args));

        vector<unique_ptr<Expr>> postConj;
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("CustomerCharges", "charge_id"));
            eq.push_back(make_unique<Var>("charge_amount"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ChargeCustomers", "charge_id"));
            eq.push_back(make_unique<Var>("charge_customer_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ChargeComplaints", "charge_id"));
            eq.push_back(make_unique<Var>("charge_complaint_id"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ChargeStatus", "charge_id"));
            eq.push_back(make_unique<Var>("STATUS_CHARGED"));
            postConj.push_back(make_unique<FuncCall>("equals", move(eq)));
        }
        {
            vector<unique_ptr<Expr>> eq;
            eq.push_back(mapVal("ComplaintStatus", "charge_complaint_id"));
            eq.push_back(make_unique<Var>("STATUS_AWAITING_PAYMENT"));
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
    globals.push_back(make_unique<Decl>("CustomerStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for complaints
    globals.push_back(make_unique<Decl>("Complaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintCustomers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintServiceType", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ComplaintPriority", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for plumbers
    globals.push_back(make_unique<Decl>("Plumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("PlumberStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for assignments
    globals.push_back(make_unique<Decl>("Assignments", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("AssignmentPlumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("AssignmentStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for quotations and spares
    globals.push_back(make_unique<Decl>("Quotations", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("QuotationComplaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("QuotationPlumbers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("QuotationSpares", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("QuotationStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("SpareCatalog", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("SpareAvailability", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Map declarations for customer charges
    globals.push_back(make_unique<Decl>("CustomerCharges", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ChargeCustomers", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ChargeComplaints", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));
    globals.push_back(make_unique<Decl>("ChargeStatus", make_unique<MapType>(
        make_unique<TypeConst>("string"), make_unique<TypeConst>("string"))));

    // Input variables for complaint
    globals.push_back(make_unique<Decl>("complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("complaint_customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("complaint_description", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("service_type", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("priority", make_unique<TypeConst>("string")));

    // Input variables for assignment
    globals.push_back(make_unique<Decl>("assignment_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("assignment_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("plumber_id", make_unique<TypeConst>("string")));

    // Input variables for acceptance
    globals.push_back(make_unique<Decl>("acceptance_assignment_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("accepting_plumber_id", make_unique<TypeConst>("string")));

    // Input variables for quotation
    globals.push_back(make_unique<Decl>("quotation_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("quotation_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("quotation_plumber_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("spare_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("quotation_amount", make_unique<TypeConst>("string")));

    // Input variables for charging
    globals.push_back(make_unique<Decl>("charge_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("charge_customer_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("charge_complaint_id", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("charge_amount", make_unique<TypeConst>("string")));

    // Status and service type constants
    globals.push_back(make_unique<Decl>("STATUS_ACTIVE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_PENDING", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ASSIGNED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_ACCEPTED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_IN_PROGRESS", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_QUOTED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_CHARGED", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_AWAITING_PAYMENT", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_AVAILABLE", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_BUSY", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("STATUS_PENDING_APPROVAL", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("SERVICE_TYPE_REPAIR", make_unique<TypeConst>("string")));
    globals.push_back(make_unique<Decl>("SPARE_NOT_IN_CATALOG", make_unique<TypeConst>("string")));

    // ─── Init empty maps ───
    vector<unique_ptr<Init>> inits;
    inits.push_back(make_unique<Init>("Customers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Complaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintCustomers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintServiceType", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ComplaintPriority", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Plumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("PlumberStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Assignments", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("AssignmentPlumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("AssignmentStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("Quotations", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("QuotationComplaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("QuotationPlumbers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("QuotationSpares", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("QuotationStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("SpareCatalog", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("SpareAvailability", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("CustomerCharges", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ChargeCustomers", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ChargeComplaints", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 
    inits.push_back(make_unique<Init>("ChargeStatus", make_unique<Map>(vector<pair<unique_ptr<Var>,unique_ptr<Expr>>>()))); 

    return Spec(std::move(globals), std::move(inits),
                std::vector<std::unique_ptr<FuncDecl>>{},
                std::move(blocks));
}

// ────────────────────────────────────────────────
// 3. Exported globals for driver
// ────────────────────────────────────────────────
Program clientProgram = buildClientProgram();
Spec    spec          = buildSpec();