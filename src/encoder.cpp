#include "../includes/encoder.hpp"
#include "encoder.hpp"

Encoder::Encoder(const vector<Item> &items, const FileType file_type, const SolverType solver_type, bool export_proof) 
: items(items), file_type(file_type), solver_type(solver_type), export_proof(export_proof) { 

    if(export_proof){
        trivial_encoding_vars = ofstream("trivial_encoding_vars.smt2", ios::out);
        trivial_encoding_constraints = ofstream("trivial_encoding_constraints.smt2", ios::out);
        trivial_encoding_domains = ofstream("trivial_encoding_domains.smt2", ios::out);
        connection_formula = ofstream("connection_formula.smt2", ios::out);
        connection2step = ofstream("connection2step.smt2", ios::out);
        domains2step = ofstream("domains2step.smt2", ios::out);
        constraints2step1 = ofstream("constraints2step1.smt2", ios::out);
        constraints2step2 = ofstream("constraints2step2.smt2", ios::out);
        sat_dom = ofstream("sat_dom.smt2", ios::out);
        sat_constraints = ofstream("sat_constraints.smt2", ios::out);
        sat_smt_funs = ofstream("sat_smt_funs.smt2", ios::out);
        smt_sat_funs = ofstream("smt_sat_funs.smt2", ios::out);
        smt_step1_funs = ofstream("smt_step1_funs.smt2", ios::out);
        left_total = ofstream("left_total.smt2", ios::out);
        left_total_step1 = ofstream("left_total_step1.smt2", ios::out);
        right_total = ofstream("right_total.smt2", ios::out);
        smt_subspace = ofstream("smt_subspace.smt2", ios::out);
        smt_subspace_step1 = ofstream("smt_subspace_step1.smt2", ios::out);
        sat_subspace = ofstream("sat_subspace.smt2", ios::out);
    }
}

// Declares the problem to be unsat
void Encoder::declare_unsat(CNF& cnf_clauses){
    
    cnf_clauses.push_back({});

    if(export_proof)
        sat_constraint_clauses.push_back({});

    unsat = true;
}

void Encoder::set_bv_limits(){
    for (auto& item : items) {
        if(holds_alternative<Constraint*>(item)){
            auto constr = get<Constraint*>(item);
            for(int i = 0; i < (int)constr->args->size(); i++){
                auto arg = *(*constr->args)[i];
                if(holds_alternative<BasicExpr*>(arg)){
                    auto expr = *get<BasicExpr*>(arg);

                    if(holds_alternative<BasicLiteralExpr*>(expr)){
                        auto basic_literal_expr = *get<BasicLiteralExpr*>(expr);

                        if(holds_alternative<SetLiteral*>(basic_literal_expr)){
                            auto set_lit = *get<SetLiteral*>(basic_literal_expr);

                            int left = numeric_limits<int>::max(), right = numeric_limits<int>::min();

                            if(holds_alternative<SetRangeLiteral*>(set_lit)){
                                auto set_range_lit = *get<SetRangeLiteral*>(set_lit);
                                left = set_range_lit.left;
                                right = set_range_lit.right;
                            } else {
                                auto set_set_lit = *get<SetSetLiteral*>(set_lit);
                                if(set_set_lit.elems->size() > 0){
                                    left = (*set_set_lit.elems)[0];
                                    right = (*set_set_lit.elems)[(*set_set_lit.elems).size() - 1];
                                }
                            }


                            if(left < bv_left)
                                bv_left = left;

                            if(right < bv_right)
                                bv_right = right;
                        }
                    }
                }
            }
        }
    }
}

// Passes through the list of items which constitute the problem
// and calls the appropriate encoder function
CNF Encoder::encode_to_cnf() {

    if(export_proof)
        set_bv_limits();


    for (auto& item : items) {
            if(unsat)
                break;
            else if(holds_alternative<Parameter*>(item))
                encode_parameter(*get<Parameter*>(item), cnf_clauses);
            else if(holds_alternative<Variable*>(item))
                encode_variable(*get<Variable*>(item), cnf_clauses);
            else if(holds_alternative<Constraint*>(item))
                encode_constraint(*get<Constraint*>(item), cnf_clauses);
            else{
                cerr << "Unknown item type in encoder\n";
                break;
            }
    }

    return cnf_clauses;
}

// Converts the encoded problem to the DIMACS format
// and writes the output to the file specified by user
void Encoder::write_to_file(){

    if(file_type == DIMACS){
        ofstream file("helper1.cnf");

        if (!file.is_open()){
            cerr << "Cannot open file\n";
            return;
        }    

        file << "p cnf " << next_dimacs_num - 1  << " " << clause_num << '\n';

        file.close();

        string command = "cat helper1.cnf helper2.cnf > formula.cnf";

        system(command.c_str());

        command = "rm helper1.cnf helper2.cnf";

        system(command.c_str());
    } else if(file_type == SMTLIB){
        ofstream file1("helper1.smt2");

        if (!file1.is_open()){
            cerr << "Cannot open file helper1.smt2\n";
            return;
        }    

        for(int i = 1; i < next_dimacs_num; i++)
            file1 << "(declare-fun x" << i << " () Bool)\n";
        
        file1 << "(assert\n";
        file1 << "(and\n";

        file1.close();

        ofstream file2("helper3.smt2");
        file2 << ")\n" << ")\n" << "(check-sat)\n" << "(get-model)\n";
        file2.close();

        string command = "cat helper1.smt2 helper2.smt2 helper3.smt2 > formula.smt2";

        system(command.c_str());

        command = "rm helper1.smt2 helper2.smt2 helper3.smt2";

        system(command.c_str());

    }
}

//Writes the clauses currently present to a DIMACS file and clears 
//the cnf_clauses vector
void Encoder::write_clauses_to_dimacs_file(CNF& cnf_clauses) {
    ofstream file("helper2.cnf", ios::app);

    string buffer;
    buffer.reserve(1 << 20); 

    for (const auto& clause : cnf_clauses) {
        for (const auto& l : clause) {

            auto key = make_tuple(l->type, l->id, l->val);

            auto it = literal_to_num.find(key);
            int lit_num;
            if (it == literal_to_num.end()) {

                lit_num = next_dimacs_num++;
                literal_to_num[key] = lit_num;
                if (l->type == LiteralType::ORDER || 
                    l->type == LiteralType::BOOL_VARIABLE || 
                    l->type == LiteralType::SET_ELEM)
                    num_to_literal[lit_num] = l;

                if(export_proof){
                    if(l->type == LiteralType::ORDER){

                        if(id_map.find(l->id) == id_map.end()){
                            string val_string = l->val < 0 ? ("(- " + to_string(-l->val) + ")") : to_string(l->val);
                            connection_formula << "(= x" << lit_num << " (<= sub_" << l->id << " " << val_string
                                        << "))\n";     
                                        
                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(<= sub_" << l->id << " " << val_string << ")\n)" << endl; 

                            left_total << "(= x" << lit_num << " " << "f_x" << lit_num << ")\n";
                        } else {
                            auto var = get<BasicVar*>(*id_map[l->id]);
                            string val_string = l->val < 0 ? ("(- " + to_string(-l->val) + ")") : to_string(l->val);
                            connection_formula << "(= x" << lit_num << " (<= " << *var->name << " " << val_string
                                        << "))\n";

                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(<= " << *var->name << " " << val_string << ")\n)" << endl;

                            left_total << "(= x" << lit_num << " f_x" << lit_num << ")\n";
                        }
                    } else if(l->type == LiteralType::BOOL_VARIABLE){
                        if(id_map.find(l->id) == id_map.end()){
                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= sub_" << l->id << " 1)\n)" << endl; 

                            left_total << "(= x" << lit_num << " " << "f_x" << lit_num << ")\n";  
                            connection_formula << "(= x" << lit_num << " (= sub_" << l->id << " 1))\n";                      
                        } else {
                            auto var = get<BasicVar*>(*id_map[l->id]);
                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= " << *var->name << " 1)\n)" << endl;

                            left_total << "(= x" << lit_num << " f_x" << lit_num << ")\n";
                            connection_formula << "(= x" << lit_num << " (= " << *var->name << " 1))\n";   
                        }
                    } else if(l->type == LiteralType::SET_ELEM){
                        if(id_map.find(l->id) == id_map.end()){
                            int ind = l->val - bv_left;

                            connection_formula << "(= x" << lit_num << "(= ((_ extract " << ind << " " << ind 
                                               << ") sub_" << l->id << ") #b1))\n";   
                                          
                            trivial_encoding_domains << "(" << (l->pol ? "= " : "distinct ") << "((_ extract " 
                                                     << ind << " " << ind 
                                                     << ") sub_" << l->id << ") #b1)\n"; 


                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= ((_ extract " << ind << " " << ind 
                                               << ") sub_" << l->id << ") #b1)\n)\n";  

                            left_total << "(= x" << lit_num << " " << "f_x" << lit_num << ")\n";
                                            
                        } else {
                            auto var = get<BasicVar*>(*id_map[l->id]);
                            int ind = l->val - bv_left;

                            connection_formula << "(= x" << lit_num << " (= ((_ extract " << ind << " " << ind 
                                               << ") " << *var->name << ") #b1))\n";
                                            
                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= ((_ extract " << ind << " " << ind 
                                               << ") " << *var->name << ") #b1)\n)\n";  

                            left_total << "(= x" << lit_num << " " << "f_x" << lit_num << ")\n";
                        }
                    } else if(l->type == LiteralType::DIRECT){
                        if(id_map.find(l->id) == id_map.end()){
                            string val_string = l->val < 0 ? ("(- " + to_string(-l->val) + ")") : to_string(l->val);
                            connection_formula << "(= x" << lit_num << " (= sub_" << l->id << " " << val_string
                                        << "))\n";     
                                        
                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= sub_" << l->id << " " << val_string << ")\n)" << endl; 

                            left_total << "(= x" << lit_num << " " << "f_x" << lit_num << ")\n";
                        } else {
                            auto var = get<BasicVar*>(*id_map[l->id]);
                            string val_string = l->val < 0 ? ("(- " + to_string(-l->val) + ")") : to_string(l->val);
                            connection_formula << "(= x" << lit_num << " (= " << *var->name << " " << val_string
                                        << "))\n";

                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= " << *var->name << " " << val_string << ")\n)" << endl;

                            left_total << "(= x" << lit_num << " f_x" << lit_num << ")\n";
                        }                        
                    }
                }
            } else {
                lit_num = it->second;
            }

            buffer.append(to_string(l->pol ? lit_num : -lit_num));
            buffer.push_back(' ');
        }
        buffer.append("0\n");
        clause_num++;

        if (buffer.size() > (1 << 20)) {
            file.write(buffer.data(), buffer.size());
            buffer.clear();
        }
    }

    if (!buffer.empty())
        file.write(buffer.data(), buffer.size());
    file.flush();

    file.close();

    if(!export_proof)
        CNF().swap(cnf_clauses);
}

//Writes the clauses currently present to a SMTLIB file and clears 
//the cnf_clauses vector
void Encoder::write_clauses_to_smtlib_file(CNF& cnf_clauses) {
    ofstream file("helper2.smt2", ios::app); 

    string buffer;
    buffer.reserve(1 << 20); 

    for (const auto& clause : cnf_clauses) {

        if(clause.size() == 0){
            buffer.append("false\n");
            // clause_num++;
            continue;
        }

        if(clause.size() > 1)
            buffer.append("(or ");

        for (const auto& l : clause) {

            auto key = make_tuple(l->type, l->id, l->val);

            int lit_num;
            auto it = literal_to_num.find(key);
            if (it == literal_to_num.end()) {
                lit_num = next_dimacs_num++;
                literal_to_num[key] = lit_num;

                if (l->type == LiteralType::ORDER ||
                    l->type == LiteralType::BOOL_VARIABLE ||
                    l->type == LiteralType::SET_ELEM)
                    num_to_literal[lit_num] = l;


                if(export_proof){
                    if(l->type == LiteralType::ORDER){

                        if(id_map.find(l->id) == id_map.end()){
                            string val_string = l->val < 0 ? ("(- " + to_string(-l->val) + ")") : to_string(l->val);
                            connection_formula << "(= x" << lit_num << " (<= sub_" << l->id << " " << val_string
                                        << "))\n";     
                                        
                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(<= sub_" << l->id << " " << val_string << ")\n)" << endl; 

                            left_total << "(= x" << lit_num << " " << "f_x" << lit_num << ")\n";
                        } else {
                            auto var = get<BasicVar*>(*id_map[l->id]);
                            string val_string = l->val < 0 ? ("(- " + to_string(-l->val) + ")") : to_string(l->val);
                            connection_formula << "(= x" << lit_num << " (<= " << *var->name << " " << val_string
                                        << "))\n";

                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(<= " << *var->name << " " << val_string << ")\n)" << endl;

                            left_total << "(= x" << lit_num << " f_x" << lit_num << ")\n";
                        }
                    } else if(l->type == LiteralType::BOOL_VARIABLE){
                        if(id_map.find(l->id) == id_map.end()){
                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= sub_" << l->id << " 1)\n)" << endl; 

                            left_total << "(= x" << lit_num << " " << "f_x" << lit_num << ")\n";  
                            connection_formula << "(= x" << lit_num << "(= sub_" << l->id << " 1))\n";                      
                        } else {
                            auto var = get<BasicVar*>(*id_map[l->id]);
                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= " << *var->name << " 1)\n)" << endl;

                            left_total << "(= x" << lit_num << " f_x" << lit_num << ")\n";
                            connection_formula << "(= x" << lit_num << "(= " << *var->name << " 1))\n";   
                        }
                    } else if(l->type == LiteralType::SET_ELEM){
                        if(id_map.find(l->id) == id_map.end()){
                            int ind = l->val - bv_left;

                            connection_formula << "(= x" << lit_num << " (= ((_ extract " << ind << " " << ind 
                                               << ") sub_" << l->id << ") #b1))\n";   
                                          
                            trivial_encoding_domains << "(" << (l->pol ? "= " : "distinct ") << "((_ extract " 
                                                     << ind << " " << ind 
                                                     << ") sub_" << l->id << ") #b1)\n"; 

                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= ((_ extract " << ind << " " << ind 
                                               << ") sub_" << l->id << ") #b1)\n)\n";  

                            left_total << "(= x" << lit_num << " " << "f_x" << lit_num << ")\n";
                                            
                        } else {
                            auto var = get<BasicVar*>(*id_map[l->id]);
                            int ind = l->val - bv_left;

                            connection_formula << "(= x" << lit_num << " (= ((_ extract " << ind << " " << ind 
                                               << ") " << *var->name << ") #b1))\n";
                                            
                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= ((_ extract " << ind << " " << ind 
                                               << ") " << *var->name << ") #b1)\n)\n";  

                            left_total << "(= x" << lit_num << " " << "f_x" << lit_num << ")\n";
                        }
                    } else if(l->type == LiteralType::DIRECT){
                        if(id_map.find(l->id) == id_map.end()){
                            string val_string = l->val < 0 ? ("(- " + to_string(-l->val) + ")") : to_string(l->val);
                            connection_formula << "(= x" << lit_num << " (= sub_" << l->id << " " << val_string
                                        << "))\n";     
                                        
                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= sub_" << l->id << " " << val_string << ")\n)" << endl; 

                            left_total << "(= x" << lit_num << " " << "f_x" << lit_num << ")\n";
                        } else {
                            auto var = get<BasicVar*>(*id_map[l->id]);
                            string val_string = l->val < 0 ? ("(- " + to_string(-l->val) + ")") : to_string(l->val);
                            connection_formula << "(= x" << lit_num << " (= " << *var->name << " " << val_string
                                        << "))\n";

                            sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool\n";
                            sat_smt_funs << "(= " << *var->name << " " << val_string << ")\n)" << endl;

                            left_total << "(= x" << lit_num << " f_x" << lit_num << ")\n";
                        }                        
                    }
                }
            } else {
                lit_num = it->second;
            }

            if (l->pol) {
                buffer.append("x");
                buffer.append(to_string(lit_num));
                buffer.push_back(' ');
            } else {
                buffer.append("(not x");
                buffer.append(to_string(lit_num));
                buffer.append(") ");
            }
        }

        if(clause.size() > 1)
            buffer.append(")\n");
        else
            buffer.append("\n");
        // clause_num++;

        if (buffer.size() > (1 << 20)) {
            file.write(buffer.data(), buffer.size());

            buffer.clear();
        }
    }

    if (!buffer.empty()){
        file.write(buffer.data(), buffer.size());
    }



    file.flush();

    file.close();

    CNF().swap(cnf_clauses);
}

void Encoder::write_lit_definition_clauses_smt_subspace(LiteralPtr lit){

    if(lit->type == SET_ELEM){
        int ind = lit->val - bv_left;
        if(id_map.find(lit->id) != id_map.end()){
            auto var = get<BasicVar*>(*id_map[lit->id]);
            if(lit->pol)
                smt_subspace << "(= ((_ extract " << ind << " " << ind 
                                << ") " << *var->name << ") #b1)\n"; 
            else
                smt_subspace << "(distinct ((_ extract " << ind << " " << ind 
                                << ") " << *var->name << ") #b1)\n"; 
        } else {
            if(lit->pol)
                smt_subspace << "(= ((_ extract " << ind << " " << ind 
                                << ") sub_" << lit->id << ") #b1)\n"; 
            else
                smt_subspace << "(distinct ((_ extract " << ind << " " << ind 
                                << ") sub_" << lit->id << ") #b1)\n";                    
        }        
        return;
    }

    if(lit->type == LiteralType::BOOL_VARIABLE){
        if(id_map.find(lit->id) != id_map.end()){
            auto var = get<BasicVar*>(*id_map[lit->id]);
            if(lit->pol)
                smt_subspace << "(= " << *var->name << " 1) ";
            else
                smt_subspace << "(not (= " << *var->name << " 1)) ";
        } else {
            if(lit->pol)
                smt_subspace << "(= sub_" << lit->id << " 1) ";
            else
                smt_subspace << "(not (= sub_" << lit->id << " 1)) ";                    
        }
        return;
    }


    CNF temp_clauses = helper_map[lit->id];

    if(temp_clauses.empty())
        return;

    Clause todo_lits;

    bool should_not = false;
    if(lit->pol == false){
        smt_subspace << "(not ";
        should_not = true;
    }

    smt_subspace << "(and\n";
    for(auto clause : temp_clauses){ 
        
        bool should_or = false;
        int counter = 0;
        for(auto lit : clause){
                counter++;
                if(counter == 2){
                    should_or = true;
                    break;
                }
        }

        if(should_or)
            smt_subspace << "(or ";

        for(auto l : clause){

            if(l->type == LiteralType::ORDER){
                
                string num_string = (l->val < 0) ? "(- " + to_string(-l->val) + ")" : to_string(l->val);

                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);

                    if(l->pol)
                        smt_subspace << "(<= " << *var->name << " " << num_string << ") ";
                    else    
                        smt_subspace << "(not (<= " << *var->name << " " << num_string << ")) ";
                } else {
                    if(l->pol)
                        smt_subspace << "(<= sub_" << l->id << " " << num_string << ") ";
                    else    
                        smt_subspace << "(not (<= sub_" << l->id << " " << num_string << ")) ";                            
                }
                
            } else if(l->type == LiteralType::BOOL_VARIABLE){
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);
                    if(l->pol)
                        smt_subspace << "(= " << *var->name << " 1) ";
                    else
                        smt_subspace << "(not (= " << *var->name << " 1)) ";
                } else {
                    if(l->pol)
                        smt_subspace << "(= sub_" << l->id << " 1) ";
                    else
                        smt_subspace << "(not (= sub_" << l->id << " 1)) ";                    
                }
            } else if(l->type == LiteralType::DIRECT){
                string num_string = (l->val < 0) ? "(- " + to_string(-l->val) + ")" : to_string(l->val);
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);
                    if(l->pol)
                        smt_subspace << "(= " << *var->name << " " << num_string << ") ";
                    else
                        smt_subspace << "(not (= " << *var->name << " " << num_string << ")) ";
                } else {
                    if(l->pol)
                        smt_subspace << "(= sub_" << l->id << " " << num_string << ") ";
                    else
                        smt_subspace << "(not (= sub_" << l->id << " " << num_string << ")) ";                    
                }                
            }else if(l->type == LiteralType::SET_ELEM){
                int ind = l->val - bv_left;
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);
                    if(l->pol)
                        smt_subspace << "(= ((_ extract " << ind << " " << ind 
                                     << ") " << *var->name << ") #b1)\n"; 
                    else
                        smt_subspace << "(distinct ((_ extract " << ind << " " << ind 
                                     << ") " << *var->name << ") #b1)\n"; 
                } else {
                    if(l->pol)
                        smt_subspace << "(= ((_ extract " << ind << " " << ind 
                                     << ") sub_" << l->id << ") #b1)\n"; 
                    else
                        smt_subspace << "(distinct ((_ extract " << ind << " " << ind 
                                     << ") sub_" << l->id << ") #b1)\n";                    
                }
                
            } else if(l->type == LiteralType::HELPER){
                write_lit_definition_clauses_smt_subspace(l);
            }
        }

        if(should_or)
            smt_subspace << ")" << endl;
    }



    if(should_not)
        smt_subspace << ")";
    smt_subspace << ")" << endl;
}

void Encoder::write_lit_definition_clauses_sat_subspace(LiteralPtr lit){

    if(lit->type == LiteralType::BOOL_VARIABLE)
        return;

    int lit_num = literal_to_num[{lit->type, lit->id, lit->val}];

    if(visited_lits.find(lit_num) != visited_lits.end())
        return;

    CNF temp_clauses = helper_map[lit->id];
    CNF temp_clauses1 = helper_map[-lit->id];

    if(temp_clauses.empty() && temp_clauses1.empty())
        return;

    visited_lits.insert(lit_num);
    Clause todo_lits;

    for(auto clause : temp_clauses){

        sat_subspace << "(or (not x" << lit_num << ") "; 
        
        for(auto l : clause){

            int lit_num1 = literal_to_num[{l->type, l->id, l->val}];
            if(l->pol)
                sat_subspace << "x" << lit_num1 << " ";
            else
                sat_subspace << "(not x" << lit_num1 << ") "; 

            if(l->type == LiteralType::HELPER && visited_lits.find(lit_num1) == visited_lits.end())
                todo_lits.push_back(l);
        }

        sat_subspace << ")" << endl;
    }

    for(auto clause : temp_clauses1){

        sat_subspace << "(or x" << lit_num << " "; 
        
        for(auto l : clause){

            int lit_num1 = literal_to_num[{l->type, l->id, l->val}];
            if(l->pol)
                sat_subspace << "x" << lit_num1 << " ";
            else
                sat_subspace << "(not x" << lit_num1 << ") "; 

            if(l->type == LiteralType::HELPER && visited_lits.find(lit_num1) == visited_lits.end())
                todo_lits.push_back(l);
        }

        sat_subspace << ")" << endl;
    }

    for(auto l : todo_lits)
        write_lit_definition_clauses_sat_subspace(l);
}

void Encoder::write_lit_definition_clauses_fun(LiteralPtr lit, bool should_define_fun){


    if(lit->type == LiteralType::BOOL_VARIABLE)
        return;

    CNF temp_clauses = helper_map[lit->id];
    CNF temp_clauses1 = helper_map[-lit->id];

    if(temp_clauses.empty() && temp_clauses1.empty())
        return;

    int lit_num = literal_to_num[{lit->type, lit->id, lit->val}];

    if(visited_lits1.find(lit_num) != visited_lits1.end())
        should_define_fun = false;
    
    if(should_define_fun){
        sat_smt_funs << "(define-fun f_x" << lit_num << " () Bool" << endl;
        visited_lits1.insert(lit_num);
    }

    if(!should_define_fun && lit->pol == false)
        sat_smt_funs << "(not" << endl;

    if(temp_clauses.size() + temp_clauses1.size() > 1)
        sat_smt_funs << "(and" << endl;
    for(auto clause : temp_clauses){

        bool should_or = false;
        int counter = 0;
        for(auto lit : clause){
            counter++;
            if(counter == 2){
                should_or = true;
                break;
            }
        }

        if(should_or)
            sat_smt_funs << "(or " << endl; 
        
        for(auto l : clause){

            if(l->type == LiteralType::ORDER){

                string num_string = l->val < 0 ? "(- " + to_string(-l->val) + ")" : to_string(l->val);
                
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);

                    if(l->pol)
                        sat_smt_funs << "(<= " << *var->name << " " << num_string << ") ";
                    else    
                        sat_smt_funs << "(not (<= " << *var->name << " " << num_string << ")) ";
                } else {
                    if(l->pol)
                        sat_smt_funs << "(<= sub_" << l->id << " " << num_string << ") ";
                    else    
                        sat_smt_funs << "(not (<= sub_" << l->id << " " << num_string << ")) ";                            
                }
            } else if(l->type == LiteralType::BOOL_VARIABLE){
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);
                    if(l->pol)
                        sat_smt_funs << "(= " << *var->name << " 1) ";
                    else
                        sat_smt_funs << "(not (= " << *var->name << " 1)) ";
                } else {
                    if(l->pol)
                        sat_smt_funs << "(= sub_" << l->id << " 1) ";
                    else
                        sat_smt_funs << "(not (= sub_" << l->id << " 1)) ";                    
                }
            }else if(l->type == LiteralType::DIRECT){
                string num_string = (l->val < 0) ? "(- " + to_string(-l->val) + ")" : to_string(l->val);
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);
                    if(l->pol)
                        sat_smt_funs << "(= " << *var->name << " " << num_string << ") ";
                    else
                        sat_smt_funs << "(not (= " << *var->name << " " << num_string << ")) ";
                } else {
                    if(l->pol)
                        sat_smt_funs << "(= sub_" << l->id << " " << num_string << ") ";
                    else
                        sat_smt_funs << "(not (= sub_" << l->id << " " << num_string << ")) ";                    
                }                
            } else if(l->type == LiteralType::SET_ELEM){
                int ind = l->val - bv_left;
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);
                    if(l->pol)
                        sat_smt_funs << "(= ((_ extract " << ind << " " << ind 
                                     << ") " << *var->name << ") #b1)\n"; 
                    else
                        sat_smt_funs << "(distinct ((_ extract " << ind << " " << ind 
                                     << ") " << *var->name << ") #b1)\n"; 
                } else {
                    if(l->pol)
                        sat_smt_funs << "(= ((_ extract " << ind << " " << ind 
                                     << ") sub_" << l->id << ") #b1)\n"; 
                    else
                        sat_smt_funs << "(distinct ((_ extract " << ind << " " << ind 
                                     << ") sub_" << l->id << ") #b1)\n";                    
                }
                
            } else if(l->type == LiteralType::HELPER){
                write_lit_definition_clauses_fun(l, false);
                todo_lits.insert(l);
            }
        }

        if(should_or)
            sat_smt_funs << ")" << endl;
    }


    if(temp_clauses1.size() > 1)
        sat_smt_funs << "(or" << endl;
    for(auto clause : temp_clauses1){

        sat_smt_funs << "(not\n";

        bool should_or = false;
        int counter = 0;
        for(auto lit : clause){
            counter++;
            if(counter == 2){
                should_or = true;
                break;
            }
        }

        if(should_or)
            sat_smt_funs << "(or \n"; 
        
        for(auto l : clause){

            if(l->type == LiteralType::ORDER){

                string num_string = l->val < 0 ? "(- " + to_string(-l->val) + ")" : to_string(l->val);
                
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);

                    if(l->pol)
                        sat_smt_funs << "(<= " << *var->name << " " << num_string << ") ";
                    else    
                        sat_smt_funs << "(not (<= " << *var->name << " " << num_string << ")) ";
                } else {
                    if(l->pol)
                        sat_smt_funs << "(<= sub_" << l->id << " " << num_string << ") ";
                    else    
                        sat_smt_funs << "(not (<= sub_" << l->id << " " << num_string << ")) ";                            
                }
            } else if(l->type == LiteralType::BOOL_VARIABLE){
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);
                    if(l->pol)
                        sat_smt_funs << "(= " << *var->name << " 1) ";
                    else
                        sat_smt_funs << "(not (= " << *var->name << " 1)) ";
                } else {
                    if(l->pol)
                        sat_smt_funs << "(= sub_" << l->id << " 1) ";
                    else
                        sat_smt_funs << "(not (= sub_" << l->id << " 1)) ";                    
                }
            }else if(l->type == LiteralType::DIRECT){
                string num_string = (l->val < 0) ? "(- " + to_string(-l->val) + ")" : to_string(l->val);
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);
                    if(l->pol)
                        sat_smt_funs << "(= " << *var->name << " " << num_string << ") ";
                    else
                        sat_smt_funs << "(not (= " << *var->name << " " << num_string << ")) ";
                } else {
                    if(l->pol)
                        sat_smt_funs << "(= sub_" << l->id << " " << num_string << ") ";
                    else
                        sat_smt_funs << "(not (= sub_" << l->id << " " << num_string << ")) ";                    
                }                
            } else if(l->type == LiteralType::SET_ELEM){
                int ind = l->val - bv_left;
                if(id_map.find(l->id) != id_map.end()){
                    auto var = get<BasicVar*>(*id_map[l->id]);
                    if(l->pol)
                        sat_smt_funs << "(= ((_ extract " << ind << " " << ind 
                                     << ") " << *var->name << ") #b1)\n"; 
                    else
                        sat_smt_funs << "(distinct ((_ extract " << ind << " " << ind 
                                     << ") " << *var->name << ") #b1)\n"; 
                } else {
                    if(l->pol)
                        sat_smt_funs << "(= ((_ extract " << ind << " " << ind 
                                     << ") sub_" << l->id << ") #b1)\n"; 
                    else
                        sat_smt_funs << "(distinct ((_ extract " << ind << " " << ind 
                                     << ") sub_" << l->id << ") #b1)\n";                    
                }
                
            } else if(l->type == LiteralType::HELPER){
                todo_lits.insert(l);
                write_lit_definition_clauses_fun(l, false);
            }
        }

        if(should_or)
            sat_smt_funs << ")" << endl;

        sat_smt_funs << ")" << endl;
    }

    if(!should_define_fun && lit->pol == false)
        sat_smt_funs << ")" << endl;
    
    if(temp_clauses1.size() > 1)
        sat_smt_funs << ")" << endl;

    if(should_define_fun)
        sat_smt_funs << ")" << endl;

    if(temp_clauses.size() + temp_clauses1.size() > 1)
        sat_smt_funs << ")" << endl;

    if(should_define_fun)
        left_total << "(= x" << lit_num << " f_x" << lit_num << ")" << endl;


}

void Encoder::write_definition_clauses() {

    if(definition_clauses.empty())
        return;
    
    for(const auto& clause : definition_clauses){
        if(clause.size() == 0){
            continue;
        }

        Clause temp_clause;

        if(clause.size() > 1)
            smt_subspace << "(or ";
        for(const auto& lit : clause){

            int lit_num = literal_to_num[{lit->type, lit->id, lit->val}];

            write_lit_definition_clauses_smt_subspace(lit);
            write_lit_definition_clauses_sat_subspace(lit);

            if(visited_lits1.find(lit_num) == visited_lits1.end())
                write_lit_definition_clauses_fun(lit, true);

            temp_clause.push_back(lit);
        }
        if(clause.size() > 1)
            smt_subspace << ")";
        smt_subspace << endl;

        if(temp_clause.size() > 1)
            sat_subspace << "(or ";
        for(auto l : temp_clause){
            if(l->pol)
                sat_subspace << "x" << literal_to_num[{l->type, l->id, l->val}] << " ";
            else
                sat_subspace << "(not x" << literal_to_num[{l->type, l->id, l->val}] << ") ";
        }
        if(temp_clause.size() > 1)
            sat_subspace << ")" << endl;
        else
            sat_subspace << endl;
    }

    for(auto l : todo_lits){
        int lit_num = literal_to_num[{l->type, l->id, l->val}];
        if(l->pol == false || visited_lits1.find(lit_num) != visited_lits1.end())
            continue;
        write_lit_definition_clauses_fun(l, true);  
    }

    sat_subspace << "---" << endl;
    smt_subspace << "---" << endl;

    todo_lits.clear();
    definition_clauses.clear();

}

void Encoder::write_sat_constraint_clauses() {

    for(const auto& clause : sat_constraint_clauses){
        if(clause.size() == 0){
            sat_constraints << "false" << endl;
            continue;
        }

        if(clause.size() > 1)
            sat_constraints << "(or ";
        for(const auto& lit : clause){
            if(lit->pol)
                sat_constraints << "x" << literal_to_num[{lit->type, lit->id, lit->val}] << " ";
            else
                sat_constraints << "(not x" << literal_to_num[{lit->type, lit->id, lit->val}] << ") ";
        }
        if(clause.size() > 1)
            sat_constraints << ")";
        sat_constraints << endl;
    }

    sat_constraints << "---\n";

    sat_constraint_clauses.clear();
}

void Encoder::write_sat_dom_clauses() {
    
    string curr_var = "";
    for(int i = 0; i < (int)sat_dom_clauses.size(); i++){
        auto clause = sat_dom_clauses[i];

        if(clause.size() == 0){
            sat_dom << "false" << endl;
            sat_subspace << "false\n---" << endl;
            continue;
        }

        string curr_name; 
        if(id_map.find(clause[0]->id) != id_map.end())
            curr_name = *get<BasicVar*>(*id_map[clause[0]->id])->name;
        else 
            curr_name = "sub_" + to_string(clause[0]->id);

        if(curr_var != curr_name && curr_var != ""){
            sat_subspace << "---" << endl;
        }

        if(clause.size() > 1){
            sat_dom << "(or ";
            sat_subspace << "(or ";
        }
        for(const auto& lit : clause){
            
            if(curr_var != curr_name){

                curr_var = curr_name;

                if(lit->type == LiteralType::ORDER){
                    smt_sat_funs << "(define-fun g_" << curr_var << " () Int\n";

                    int left = lit->val;
                    auto next_lit = sat_dom_clauses[i+1][0];
                    int right = next_lit->val;

                    int first_lit_num = literal_to_num[{lit->type, lit->id, lit->val}];
                    string num_string = left < 0 ? "(- " + to_string(-left) + ")" : to_string(left);

                    smt_sat_funs << "(ite x" << first_lit_num << " " << num_string << " ";
                    for(int i = left + 2; i <= right; i++){
                        num_string = i - 1 < 0 ? "(- " + to_string(-(i - 1)) + ")" : to_string(i - 1);
                        smt_sat_funs << "(ite x" << first_lit_num + (i - left) << " " << num_string << " "; 
                    }
                    num_string = right < 0 ? "(- " + to_string(-right) + ")" : to_string(right);
                    smt_sat_funs << "(ite x" << first_lit_num + 1 << " " << num_string << " ";

                    num_string = right + 1 < 0 ? "(- " + to_string(-(right + 1)) + ")" : to_string(right + 1);
                    smt_sat_funs << num_string;

                    for(int i = left; i <= right; i++)
                        smt_sat_funs << ")";
                    smt_sat_funs << "\n)" << endl;

                    right_total << "(= " << curr_var << " g_" << curr_var << ")\n";
                } else if(lit->type == LiteralType::BOOL_VARIABLE){
                    smt_sat_funs << "(define-fun g_" << curr_var << " () Int\n";

                    smt_sat_funs << "(ite x" << literal_to_num[{lit->type, lit->id, lit->val}] << " 1 0)";
                    smt_sat_funs << "\n)" << endl;

                    right_total << "(= " << curr_var << " g_" << curr_var << ")\n";
                } else if(lit->type == LiteralType::SET_ELEM){
                    if(lit->pol == true)
                        sat_subspace << "(= x" << literal_to_num[{lit->type, lit->id, lit->val}] << " true)" << endl;
                    else
                        sat_subspace << "(= x" << literal_to_num[{lit->type, lit->id, lit->val}] << " false)" << endl;                        
                }

            }

            if(lit->pol){
                sat_dom << "x" << literal_to_num[{lit->type, lit->id, lit->val}] << " ";
                sat_subspace << "x" << literal_to_num[{lit->type, lit->id, lit->val}] << " ";
            } else {
                sat_dom << "(not x" << literal_to_num[{lit->type, lit->id, lit->val}] << ") ";
                sat_subspace << "(not x" << literal_to_num[{lit->type, lit->id, lit->val}] << ") ";
            }
        }
        if(clause.size() > 1){
            sat_dom << ")";
            sat_subspace << ")";
        }
        sat_dom << endl;
        sat_subspace << endl;
    }

    if(!sat_dom_clauses.empty())
        sat_subspace << "---" << endl;
    

    sat_dom_clauses.clear();
}

void Encoder::handle_set_vars(){
    for(auto &var : set_vars){
        int j = 0;
        auto elems = get_set_elems(*var);

        smt_sat_funs << "(define-fun g_" << *var->name << " () (_ BitVec \n";

        if((*elems).size() > 0)
            smt_sat_funs << "(bvor\n";

        int bv_diff = bv_right - bv_left + 1;
        for(int i = bv_left; i <= bv_right; i++){
            int lit_num = literal_to_num[{LiteralType::SET_ELEM, var->id, i}];
            if(j < (int)(*elems).size() && (*elems)[j] == i){
                j++;

                smt_sat_funs << "(ite x" << lit_num << " #b";
                
                for(int k = i + 1; k <= bv_right; k++)
                    smt_sat_funs << "0";
                smt_sat_funs << "1";
                for(int k = bv_left; k < i; k++)
                    smt_sat_funs << "0";

                smt_sat_funs << " #b";
                for(int k = 0; k < bv_diff; k++)
                    smt_sat_funs << "0";
                smt_sat_funs << ")\n";

            } else {
                trivial_encoding_domains << "(distinct ((_ extract " << i - bv_left << " " << i - bv_left << ") " 
                                        << *var->name << ") #b1)" << endl;
                smt_subspace << "(distinct ((_ extract " << i - bv_left << " " << i - bv_left << ") " 
                                        << *var->name << ") #b1)\n---" << endl;
            }
        }

        if((*elems).size() > 0)
            smt_sat_funs << ")\n)" << endl;
        else {
            smt_sat_funs << "(_ bv0 " << bv_right - bv_left + 1 << ")\n)\n" << endl;
        }
        
        right_total << "(= " << *var->name << " g_" << *var->name << ")" << endl;
    }
}

void Encoder::handle_set_in_constraints(){
    for(auto [var, set] : set_in_pairs){
        string ind = "(- " + var + " " + to_string(bv_left) + ")";
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= ((_ extract 0 0) (bvlshr " << set << " ((_ int2bv "
                                     << bv_right - bv_left + 1 << ") (- " << var
                                     << " " << bv_left << ")))) #b1)\n)" << endl; 
    }

    for(auto [var, set, r] : set_in_reif_pairs){
        string ind = "(- " + var + " " + to_string(bv_left) + ")";
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << r << " (ite (= ((_ extract 0 0) (bvlshr " << set << " ((_ int2bv "
                                     << bv_right - bv_left + 1 << ") (- " << var
                                     << " " << bv_left << ")))) #b1) 1 0))\n)" << endl; 
    }

    for(auto [var, set, r] : set_in_imp_pairs){
        string ind = "(- " + var + " " + to_string(bv_left) + ")";
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << r << " 1) (= ((_ extract 0 0) (bvlshr " << set << " ((_ int2bv "
                                     << bv_right - bv_left + 1 << ") (- " << var
                                     << " " << bv_left << ")))) #b1))\n)" << endl; 
    }
}

void Encoder::write_ones(ofstream& proof_file){

    int bv_diff = bv_right - bv_left + 1;

    proof_file << "(define-fun ones ((?x (_ BitVec " << bv_diff << "))) Int\n";
    proof_file << "(+\n";
    for(int i = 0; i < bv_diff; i++){
        proof_file << "(bv2nat ((_ extract " << i << " " << i << ") ?x))\n"; 
    }   
    proof_file << "))\n";
}

void Encoder::write_mod_div(ofstream& proof_file){
    proof_file <<
    "(define-fun mzn_mod_f ((x Int) (y Int)) Int\n"
    "    (ite (and (< x 0) (distinct (mod x y) 0))\n"
    "            (- (mod x y) (abs y))\n"
    "\t    (mod x y)\n"
    "    )\n"
    ")\n"
    "\n"
    "(define-fun mzn_mod ((x Int) (y Int) (z Int)) Bool\n"
    "  (and\n"
    "    (distinct y 0)\n"
    "    (= z (mzn_mod_f x y))\n"
    "  )\n"
    ")\n"
    "\n"
    "(define-fun sgn ((x Int)) Int\n"
    "  (ite (> x 0) 1 (ite (< x 0) (- 1) 0))\n"
    ")\n"
    "\n"
    "(define-fun mzn_div_f ((x Int) (y Int)) Int\n"
    "  (ite (and (< x 0) (distinct (mod x y) 0))\n"
    "        (+ (div x y) (sgn y))\n"
    "\t(div x y)\n"
    "  )\n"
    ")\n"
    "\n"
    "(define-fun mzn_div ((x Int) (y Int) (z Int)) Bool\n"
    "  (and\n"
    "    (distinct y 0)\n"
    "    (= z (mzn_div_f x y))\n"
    "  )\n"
    ")\n";

}

void Encoder::write_lex(ofstream& proof_file){

    int bv_diff = bv_right - bv_left + 1;
    proof_file << "(define-fun leftmost_one ((?x (_ BitVec " << bv_diff << "))) Int\n";
    proof_file << "(+ " << ((bv_left < 0) ? ("(- " + to_string(-bv_left) + ")") : to_string(bv_left)) << "\n";

    for(int i = bv_diff - 1; i >= 0; i--){
        proof_file << "(ite (= (bvand (bvlshr ?x (_ bv" << i << " " << bv_diff << ")) (_ bv1 "
                   << bv_diff << ")) (_ bv1 " << bv_diff << ")) " 
                   << i << " \n";
    }

    proof_file << "(- 1))\n";
    for(int i = bv_left; i <= bv_right; i++)
        proof_file << ")";
    proof_file << "\n)\n" << endl;

    proof_file << "(define-fun rightmost_one ((?x (_ BitVec " << bv_diff << "))) Int\n";
    proof_file << "(+ " << ((bv_left < 0) ? ("(- " + to_string(-bv_left) + ")") : to_string(bv_left)) << "\n";

    for(int i = 0; i < bv_diff; i++){
        proof_file << "(ite (= (bvand (bvlshr ?x (_ bv" << i << " " << bv_diff << ")) (_ bv1 "
                   << bv_diff << ")) (_ bv1 " << bv_diff << ")) " 
                   << i << " \n";
    }

    proof_file << "(- 1))\n";
    for(int i = bv_left; i <= bv_right; i++)
        proof_file << ")";
    proof_file << "\n)\n" << endl;

    proof_file << "(define-fun rev ((?x (_ BitVec " << bv_diff << "))) (_ BitVec " << bv_diff << ")\n";
    proof_file << "(concat\n";
    for(int i = 0; i < bv_diff; i++){
        proof_file << "((_ extract " << i << " " << i << ") ?x)\n"; 
    }
    proof_file << ")\n)\n" << endl;

    proof_file << "(define-fun prefix ((?x (_ BitVec " << bv_diff << ")) (?y (_ BitVec " << bv_diff << "))) Bool\n";
    proof_file << "(or\n";
    proof_file << "(= ?x (_ bv0 " << bv_diff << "))\n";
    for(int i = 1; i < bv_diff; i++){
        proof_file << "(= (rev ?x) (bvand (rev ?y) #b";
        for(int j = 0; j < i; j++)
            proof_file << "1";
        for(int j = i; j < bv_diff; j++)
            proof_file << "0";

        proof_file << "))\n";
    }
    proof_file << "(= (rev ?x) (rev ?y))\n)\n)\n" << endl;

}

void Encoder::flush_buffers(){
    trivial_encoding_vars.flush();
    trivial_encoding_constraints.flush();
    trivial_encoding_domains.flush();
    connection_formula.flush();
    sat_smt_funs.flush();
    smt_sat_funs.flush();
    left_total.flush();
    right_total.flush();
    smt_subspace.flush();
    sat_subspace.flush();

    if(is2step){
        connection2step.flush();
        domains2step.flush();
        constraints2step1.flush();
        constraints2step2.flush();
        smt_step1_funs.flush();
        left_total_step1.flush();
        smt_subspace_step1.flush();
    }
}

void Encoder::generate_proof(){

    if(is2step){
        generate_proof2step();
        return;
    }

    system("rm -f proof.smt2");
    ofstream proof_file = ofstream("proof.smt2", ios::app);
    flush_buffers();

    proof_file << "(set-option :produce-models true)\n";
    proof_file << "(set-option :produce-proofs true)\n";

    //Setting logic
    if(isBV && isLIA){
        proof_file << "(set-logic ALL";
    } else {    
        proof_file << "(set-logic QF_";
        if(isUF || isBV)
            proof_file << "UF";
        if(isBV)
            proof_file << "BV";
        if(isNIA)
            proof_file << "NIA";
        else if(isLIA)
            proof_file << "LIA";
    }
    proof_file << ")\n" << endl;

    if(needLex) 
        write_lex(proof_file);

    //Setting BitVec sizes
    int bv_diff = bv_right - bv_left + 1;

    handle_set_vars();
    handle_set_in_constraints();
    if(needOnes)
        write_ones(proof_file);

    string command =
        "awk '/BitVec/{$0=$0\"" + std::to_string(bv_diff) + "))\"}1' "
        "trivial_encoding_vars.smt2 > tmp && mv tmp trivial_encoding_vars.smt2";

    system(command.c_str());

    command =
        "awk '/define-fun/ { gsub(/BitVec/, \"BitVec " +
        std::to_string(bv_diff) +
    ")\") } 1' smt_sat_funs.smt2 > tmp && mv tmp smt_sat_funs.smt2";


    system(command.c_str());

    system("cat trivial_encoding_vars.smt2 >> proof.smt2");

    int num_vars = 0;
    ifstream formula("formula.cnf");
    string dummy;
    formula >> dummy >> dummy >> num_vars;  
    formula.close();

    for(int i = 1; i <= num_vars; i++){
        proof_file << "(declare-const x" << i << " Bool)\n";
    }
    proof_file << endl;

    proof_file << "(define-fun smt_dom () Bool\n";

    if(std::filesystem::file_size("trivial_encoding_domains.smt2") > 0){
        proof_file << "(and " << endl;
        system("cat trivial_encoding_domains.smt2 >> proof.smt2");
        proof_file << ")\n)" << endl;
    } else {
        proof_file << "true\n)\n";
    }

    system("cat trivial_encoding_constraints.smt2 >> proof.smt2");

    proof_file << "(define-fun smt_encode () Bool\n";
    proof_file << "(and\n";
    proof_file << "smt_dom\n";
    for(int i = 1; i < next_constraint_num; i++)
        proof_file << "smt_c" << i << endl;
    proof_file << ")\n)\n";

    proof_file << "(define-fun sat_dom () Bool\n";

    if(std::filesystem::file_size("sat_dom.smt2") > 0){
        proof_file << "(and " << endl;
        system("cat sat_dom.smt2 >> proof.smt2");
        proof_file << ")\n)\n";
    } else {
        proof_file << "true\n)\n";
    }

    ifstream sat_constraints_file("sat_constraints.smt2");
    int k = 1;

    proof_file << "(define-fun sat_c" << k++ << " () Bool\n";
    proof_file << "(and " << endl;
    string line;
    while(getline(sat_constraints_file, line)){
        if(line == "---"){
            proof_file << ")\n)" << endl;

            proof_file << "(define-fun sat_c" << k++ << " () Bool\n";
            proof_file << "(and " << endl;
        } else
            proof_file << line << endl;
    }
    proof_file << ")\n)" << endl;

    proof_file << "(define-fun sat_encode () Bool\n";
    proof_file << "(and\n";
    proof_file << "sat_dom\n";
    for(int i = 1; i < next_constraint_num; i++)
        proof_file << "sat_c" << i << endl;
    proof_file << ")\n)\n";

    ifstream smt_sat_rel_reader = ifstream("connection_formula.smt2");

    if(std::filesystem::file_size("connection_formula.smt2") > 0)
        proof_file << "(define-fun smt_sat_rel" << smt_sat_rel_num++ << " () Bool\n(and\n"; 

    int i = 0, granulation = 50;
    bool should_define_fun = false;
    while(getline(smt_sat_rel_reader, line)){

        if(should_define_fun){
            proof_file << "(define-fun smt_sat_rel" << smt_sat_rel_num++ << " () Bool\n(and\n";
            should_define_fun = false; 
        }

        proof_file << line << endl;

        if(i == granulation){
            proof_file << ")\n)\n";
            should_define_fun = true;  
            i = 0;
        }

        i++;
    }
    if(i != 1)
        proof_file << ")\n)\n";

    proof_file << "(define-fun smt_sat_rel () Bool\n";
    if(smt_sat_rel_num > 2)
        proof_file << "(and\n";
    for(int i = 1; i < smt_sat_rel_num; i++)
        proof_file << "smt_sat_rel" << i << "\n";
    if(smt_sat_rel_num > 2)
        proof_file << ")\n";
    proof_file << ")\n";

    ifstream smt_subspace_reader = ifstream("smt_subspace.smt2");
    if(std::filesystem::file_size("smt_subspace.smt2") > 0)
        proof_file << "(define-fun smt_subspace" << smt_subspace_num++ << " () Bool\n(and\n"; 

    should_define_fun = false;
    while(getline(smt_subspace_reader, line)){

        if(should_define_fun){
            proof_file << "(define-fun smt_subspace" << smt_subspace_num++ << " () Bool\n(and\n";
            should_define_fun = false; 
        }

        if(line == "---"){
            proof_file << ")\n)\n";
            should_define_fun = true;    
        } else
            proof_file << line << endl;
    }

    proof_file << "(define-fun smt_subspace () Bool\n";
    if(smt_subspace_num == 1){
        proof_file << "true\n)" << endl;
    } else {
        if(smt_subspace_num > 2)
            proof_file << "(and\n";
        for(int i = 1; i < smt_subspace_num; i++)
            proof_file << "smt_subspace" << i << "\n";
        if(smt_subspace_num > 2)
            proof_file << ")\n";
        proof_file << ")\n";
    }

    ifstream sat_subspace_reader = ifstream("sat_subspace.smt2");
    if(std::filesystem::file_size("sat_subspace.smt2") > 0)
        proof_file << "(define-fun sat_subspace" << sat_subspace_num++ << " () Bool\n(and\n"; 

    should_define_fun = false;
    while(getline(sat_subspace_reader, line)){

        if(should_define_fun){
            proof_file << "(define-fun sat_subspace" << sat_subspace_num++ << " () Bool\n(and\n";
            should_define_fun = false; 
        }

        if(line == "---"){
            proof_file << ")\n)\n";
            should_define_fun = true;    
        } else
            proof_file << line << endl;
    }

    proof_file << "(define-fun sat_subspace () Bool\n";
    if(sat_subspace_num == 1){
        proof_file << "true\n)" << endl;
    } else {
        if(sat_subspace_num > 2)
            proof_file << "(and\n";
        for(int i = 1; i < sat_subspace_num; i++)
            proof_file << "sat_subspace" << i << "\n";
        if(sat_subspace_num > 2)
            proof_file << ")\n";
        proof_file << ")" << endl;
    }

    system("cat sat_smt_funs.smt2 >> proof.smt2");

    system("cat smt_sat_funs.smt2 >> proof.smt2");

    for(int i = 1; i < smt_subspace_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check SMT containing " << i << "\")\n";
        proof_file << "(assert (and smt_encode (not smt_subspace" << i << ")))\n";

        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"smt_containing_proof" << i <<".out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }


    for(int i = 1; i < sat_subspace_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check SAT containing " << i << "\")\n";
        proof_file << "(assert (and sat_encode (not sat_subspace" << i << ")))\n";

        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"sat_containing_proof" << i <<".out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }

    for(int i = 1; i < smt_sat_rel_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check left-total R" << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "smt_subspace" << endl;
        system("cat left_total.smt2 >> proof.smt2");
        proof_file << "(not smt_sat_rel" << i << ")\n";
        proof_file << ")\n)\n";
        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"left_total_r" << i << "_proof.out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";
    }

    for(int i = 1; i < sat_subspace_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check left-total " << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "smt_subspace" << endl;
        system("cat left_total.smt2 >> proof.smt2");
        proof_file << "(not sat_subspace" << i << ")\n";
        proof_file << ")\n)\n";
        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"left_total_" << i << "_proof.out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }

    for(int i = 1; i < smt_sat_rel_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check right-total R" << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "sat_subspace" << endl;
        system("cat right_total.smt2 >> proof.smt2");
        proof_file << "(not smt_sat_rel" << i << ")\n";
        proof_file << ")\n)\n";
        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"right_total_r" << i << "_proof.out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";
    }

    for(int i = 1; i < smt_subspace_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check right-total " << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "sat_subspace" << endl;
        system("cat right_total.smt2 >> proof.smt2");
        proof_file << "(not smt_subspace" << i << ")\n";
        proof_file << ")\n)\n";
        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"right_total_" << i << "_proof.out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }

    proof_file << "\n";

    proof_file << "(push)\n";
    proof_file << "(echo \"Check soundness dom\")\n";
    proof_file << "(assert (and\n";
    proof_file << "smt_subspace\n";
    proof_file << "sat_subspace\n";
    proof_file << "smt_sat_rel\n";
    proof_file << "(distinct smt_dom sat_dom)\n";
    proof_file << ")\n";
    proof_file << ")\n";

    proof_file << "(check-sat)\n";
    proof_file << "(set-option :regular-output-channel \"soundness_proof_dom.out\")\n";
    proof_file << "(get-proof)\n";
    proof_file << "(set-option :regular-output-channel \"stdout\")\n";
    proof_file << "(pop)\n\n";

    for(int i = 1; i < next_constraint_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check soundness c" << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "           smt_subspace\n";
        proof_file << "           sat_subspace\n";
        proof_file << "           smt_sat_rel\n";
        proof_file << "           (distinct smt_c" << i << " sat_c" << i << ")\n";
        proof_file << "        )\n";
        proof_file << ")\n";

        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"soundness_proof_c" << i <<".out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }


    system("rm -f helper2.smt2 connection_formula.smt2 trivial*.smt2 sat_dom.smt2 *subspace.smt2");
    system("rm -f left_containing.smt2 right_containing.smt2 left_total.smt2 right_total.smt2 sat_constraints.smt2");
    system("rm -f sat_smt_funs.smt2 smt_sat_funs.smt2");
    system("rm -f connection2step.smt2 constraints2step1.smt2 constraints2step2.smt2 domains2step.smt2");
    system("rm -f left_total_step1.smt2 smt_step1_funs.smt2 smt_subspace_step1.smt2");

    system("mkdir -p proofs");
    system("mv proof.smt2 proofs");

    proof_file.close();
}

void Encoder::generate_proof2step(){
    system("rm -f proof_step1.smt2");
    ofstream proof_file = ofstream("proof_step1.smt2", ios::app);
    flush_buffers();

    proof_file << "(set-option :produce-models true)\n";
    proof_file << "(set-option :produce-proofs true)\n";

    //Setting logic
    if(isBV && isLIA){
        proof_file << "(set-logic ALL";
    } else {    
        proof_file << "(set-logic QF_";
        if(isUF || isBV)
            proof_file << "UF";
        if(isBV)
            proof_file << "BV";
        if(isNIA)
            proof_file << "NIA";
        else if(isLIA)
            proof_file << "LIA";
    }
    proof_file << ")\n" << endl;

    //Setting BitVec sizes
    int bv_diff = bv_right - bv_left + 1;

    handle_set_vars();
    handle_set_in_constraints();
    if(needOnes)
        write_ones(proof_file);
    if(needModDiv)
        write_mod_div(proof_file);
    if(needLex)
        write_lex(proof_file);

    string command =
        "awk '/BitVec/{$0=$0\"" + std::to_string(bv_diff) + "))\"}1' "
        "trivial_encoding_vars.smt2 > tmp && mv tmp trivial_encoding_vars.smt2";

    system(command.c_str());

    command =
        "awk '/define-fun/ { gsub(/BitVec/, \"BitVec " +
        std::to_string(bv_diff) +
    ")\") } 1' smt_sat_funs.smt2 > tmp && mv tmp smt_sat_funs.smt2";


    system(command.c_str());

    system("cat trivial_encoding_vars.smt2 >> proof_step1.smt2");

    proof_file << "\n(define-fun smt_dom_step1 () Bool\n";

    if(std::filesystem::file_size("trivial_encoding_domains.smt2") > 0){
        proof_file << "(and " << endl;
        system("cat trivial_encoding_domains.smt2 >> proof_step1.smt2");
        proof_file << ")\n)" << endl;
    } else {
        proof_file << "true\n)\n";
    }

    system("cat trivial_encoding_constraints.smt2 >> proof_step1.smt2");
    system("cat constraints2step1.smt2 >> proof_step1.smt2");
    

    proof_file << "(define-fun smt_encode_step1 () Bool\n";
    proof_file << "(and\n";
    proof_file << "smt_dom_step1\n";
    for(int i = 1; i < next_constraint_num; i++){
        if(constraint2step_set.find(i) != constraint2step_set.end())
            proof_file << "smt_c" << i << "_step1" << endl;
        else
            proof_file << "smt_c" << i << endl;
    }
    proof_file << ")\n)\n";

    proof_file << "(define-fun smt_dom () Bool\n";

    if(std::filesystem::file_size("trivial_encoding_domains.smt2") > 0 || std::filesystem::file_size("domains2step.smt2") > 0){
        proof_file << "(and " << endl;
        system("cat trivial_encoding_domains.smt2 >> proof_step1.smt2");
        system("cat domains2step.smt2 >> proof_step1.smt2");
        proof_file << ")\n)" << endl;
    } else {
        proof_file << "true\n)\n";
    }

    system("cat constraints2step2.smt2 >> proof_step1.smt2");

    proof_file << "(define-fun smt_encode () Bool\n";
    proof_file << "(and\n";
    proof_file << "smt_dom\n";
    for(int i = 1; i < next_constraint_num; i++){
        proof_file << "smt_c" << i << endl;
    }
    proof_file << ")\n)\n";

    proof_file << "(define-fun smt_step1_rel() Bool\n";
    proof_file << "true\n)\n";
    
    bool should_define_fun = false;
    string line;

    ifstream smt_subspace_reader = ifstream("smt_subspace_step1.smt2");
    if(std::filesystem::file_size("smt_subspace_step1.smt2") > 0)
        proof_file << "(define-fun smt_subspace_step1_" << smt_subspace_step1_num++ <<" () Bool\n(and\n"; 

    
    while(getline(smt_subspace_reader, line)){

        if(should_define_fun){
            proof_file << "(define-fun smt_subspace_step1_" << smt_subspace_step1_num++ <<" () Bool\n(and\n";
            should_define_fun = false; 
        }

        if(line == "---"){
            proof_file << ")\n)\n";
            should_define_fun = true;    
        } else {
            if(line[0] == '!')
                proof_file << line.substr(1, line.size());
            else
                proof_file << line << endl;
        }
    }

    proof_file << "(define-fun smt_subspace_step1 () Bool\n";
    if(smt_subspace_step1_num == 1){
        proof_file << "true\n)\n";
    } else {
        if(smt_subspace_step1_num > 2)
            proof_file << "(and\n";
        for(int i = 1; i < smt_subspace_step1_num; i++)
            proof_file << "smt_subspace_step1_" << i << "\n";
        if(smt_subspace_step1_num > 2)
            proof_file << ")\n";
        proof_file << ")\n";
    }

    smt_subspace_reader = ifstream("smt_subspace_step1.smt2");
    if(std::filesystem::file_size("smt_subspace_step1.smt2") > 0)
        proof_file << "(define-fun smt_subspace" << smt_subspace_step2_num++ << " () Bool\n(and\n"; 

    should_define_fun = false;
    while(getline(smt_subspace_reader, line)){

        if(should_define_fun){
            proof_file << "(define-fun smt_subspace" << smt_subspace_step2_num++ << " () Bool\n(and\n";
            should_define_fun = false; 
        }

        if(line == "---"){
            proof_file << ")\n)\n";
            should_define_fun = true;    
        } else if(line[0] == '!'){
            getline(smt_subspace_reader, line);
        } else 
            proof_file << line << endl;
    }

    ifstream connection2step_reader = ifstream("connection2step.smt2");
    if((std::filesystem::file_size("connection2step.smt2") > 0 && should_define_fun) || std::filesystem::file_size("smt_subspace_step1.smt2") == 0)
        proof_file << "(define-fun smt_subspace" << smt_subspace_step2_num++ << " () Bool\n(and\n"; 

    should_define_fun = false;    
    while(getline(connection2step_reader, line)){

        if(should_define_fun){
            proof_file << "(define-fun smt_subspace" << smt_subspace_step2_num++ << " () Bool\n(and\n";
            should_define_fun = false; 
        }

        if(line == "---"){
            proof_file << ")\n)" << endl;
            should_define_fun = true;    
        } else
            proof_file << line << endl;
    }

    proof_file << "(define-fun smt_subspace () Bool\n";
    if(smt_subspace_step2_num > 2)
        proof_file << "(and\n";
    for(int i = 1; i < smt_subspace_step2_num; i++)
        proof_file << "smt_subspace" << i << "\n";
    if(smt_subspace_step2_num > 2)
        proof_file << ")\n";
    proof_file << ")" << endl;
    
    system("cat smt_step1_funs.smt2 >> proof_step1.smt2");

    system("mkdir -p proofs_step1");

    for(int i = 1; i < smt_subspace_step1_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check SMT step 1 containing " << i << "\")\n";
        proof_file << "(assert (and smt_encode_step1 (not smt_subspace_step1_" << i << ")))\n";

        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"smt_containing_step1_proof" << i <<".out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }


    for(int i = 1; i < smt_subspace_step2_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check SMT step 2 containing " << i << "\")\n";
        proof_file << "(assert (and smt_encode (not smt_subspace" << i << ")))\n";

        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"smt_containing_step2_proof" << i <<".out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }


    proof_file << "(push)\n";
    proof_file << "(echo \"Check left-total step 1 R\")\n";
    proof_file << "(assert (and\n";
    proof_file << "smt_subspace_step1" << endl;
    system("cat left_total_step1.smt2 >> proof_step1.smt2");
    proof_file << "(not smt_step1_rel )\n";
    proof_file << ")\n)\n";
    proof_file << "(check-sat)\n";
    proof_file << "(set-option :regular-output-channel \"left_total_step1_r_proof.out\")\n";
    proof_file << "(get-proof)\n";
    proof_file << "(set-option :regular-output-channel \"stdout\")\n";
    proof_file << "(pop)\n\n";
    

    for(int i = 1; i < smt_subspace_step2_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check left-total step 1 " << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "smt_subspace_step1" << endl;
        system("cat left_total_step1.smt2 >> proof_step1.smt2");
        proof_file << "(not smt_subspace" << i << ")\n";
        proof_file << ")\n)\n";
        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"left_total_step1_" << i << "_proof.out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }

    proof_file << "(push)\n";
    proof_file << "(echo \"Check right-total step 1 R\")\n";
    proof_file << "(assert (and\n";
    proof_file << "smt_subspace" << endl;
    proof_file << "(not smt_step1_rel )\n";
    proof_file << ")\n)\n";
    proof_file << "(check-sat)\n";
    proof_file << "(set-option :regular-output-channel \"right_total_step1_r_proof.out\")\n";
    proof_file << "(get-proof)\n";
    proof_file << "(set-option :regular-output-channel \"stdout\")\n";
    proof_file << "(pop)\n\n";

    for(int i = 1; i < smt_subspace_step1_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check right-total " << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "smt_subspace" << endl;
        proof_file << "(not smt_subspace_step1_" << i << ")\n";
        proof_file << ")\n)\n";
        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"right_total_step1_" << i << "_proof.out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }



    proof_file << "(push)\n";
    proof_file << "(echo \"Check soundness dom step 1\")\n";
    proof_file << "(assert (and\n";
    proof_file << "smt_subspace_step1\n";
    proof_file << "smt_subspace\n";
    proof_file << "smt_step1_rel\n";
    proof_file << "(distinct smt_dom_step1 smt_dom)\n";
    proof_file << ")\n";
    proof_file << ")\n";
    proof_file << "(check-sat)\n";
    proof_file << "(set-option :regular-output-channel \"soundness_proof_dom.out\")\n";
    proof_file << "(get-proof)\n";
    proof_file << "(set-option :regular-output-channel \"stdout\")\n";
    proof_file << "(pop)\n\n";

    for(int i = 1; i < next_constraint_num; i++){
        if(constraint2step_set.find(i) != constraint2step_set.end()){
            proof_file << "(push)\n";
            proof_file << "(echo \"Check soundness c" << i << " step 1\")\n";
            proof_file << "(assert (and\n";
            proof_file << "           smt_subspace_step1\n";
            proof_file << "           smt_subspace\n";
            proof_file << "           smt_step1_rel\n";
            proof_file << "           (distinct smt_c" << i << "_step1 smt_c" << i << ")\n";
            proof_file << "        )\n";
            proof_file << ")\n";

            proof_file << "(check-sat)\n";
            proof_file << "(set-option :regular-output-channel \"soundness_proof_c" << i <<".out\")\n";
            proof_file << "(get-proof)\n";
            proof_file << "(set-option :regular-output-channel \"stdout\")\n";
            proof_file << "(pop)\n\n";
        }

    }

    proof_file.close();
    system("rm -f proof.smt2");
    proof_file = ofstream("proof.smt2", ios::app);

    proof_file << "(set-option :produce-models true)\n";
    proof_file << "(set-option :produce-proofs true)\n";

    //Setting logic
    if(isBV && isLIA){
        proof_file << "(set-logic ALL";
    } else {    
        proof_file << "(set-logic QF_";
        if(isUF || isBV)
            proof_file << "UF";
        if(isBV)
            proof_file << "BV";
        if(isNIA)
            proof_file << "NIA";
        else if(isLIA)
            proof_file << "LIA";
    }
    proof_file << ")\n" << endl;

    if(needLex)
        write_lex(proof_file);

    system("cat trivial_encoding_vars.smt2 >> proof.smt2");

    int num_vars = 0;
    ifstream formula("formula.cnf");
    string dummy;
    formula >> dummy >> dummy >> num_vars;  
    formula.close();

    for(int i = 1; i <= num_vars; i++){
        proof_file << "(declare-const x" << i << " Bool)\n";
    }
    proof_file << endl;

    proof_file << "(define-fun smt_dom () Bool\n";

    if(std::filesystem::file_size("trivial_encoding_domains.smt2") > 0 || 
       std::filesystem::file_size("domains2step.smt2") > 0){
        proof_file << "(and " << endl;
        system("cat trivial_encoding_domains.smt2 >> proof.smt2");
        system("cat domains2step.smt2 >> proof.smt2");
        proof_file << ")\n)" << endl;
    } else {
        proof_file << "true\n)\n";
    }

    system("cat trivial_encoding_constraints.smt2 >> proof.smt2");
    system("cat constraints2step2.smt2 >> proof.smt2");


    proof_file << "(define-fun smt_encode () Bool\n";
    proof_file << "(and\n";
    proof_file << "smt_dom\n";
    for(int i = 1; i < next_constraint_num; i++)
        proof_file << "smt_c" << i << endl;
    proof_file << ")\n)\n";

    proof_file << "(define-fun sat_dom () Bool\n";

    if(std::filesystem::file_size("sat_dom.smt2") > 0){
        proof_file << "(and " << endl;
        system("cat sat_dom.smt2 >> proof.smt2");
        proof_file << ")\n)\n";
    } else {
        proof_file << "true\n)\n";
    }

    ifstream sat_constraints_file("sat_constraints.smt2");
    int k = 1;

    proof_file << "(define-fun sat_c" << k++ << " () Bool\n";
    proof_file << "(and " << endl;
    
    while(getline(sat_constraints_file, line)){
        if(line == "---"){
            proof_file << ")\n)" << endl;

            proof_file << "(define-fun sat_c" << k++ << " () Bool\n";
            proof_file << "(and " << endl;
        } else
            proof_file << line << endl;
    }
    proof_file << ")\n)" << endl;

    proof_file << "(define-fun sat_encode () Bool\n";
    proof_file << "(and\n";
    proof_file << "sat_dom\n";
    for(int i = 1; i < next_constraint_num; i++)
        proof_file << "sat_c" << i << endl;
    proof_file << ")\n)\n";

    ifstream smt_sat_rel_reader = ifstream("connection_formula.smt2");

    if(std::filesystem::file_size("connection_formula.smt2") > 0)
        proof_file << "(define-fun smt_sat_rel" << smt_sat_rel_num++ << " () Bool\n(and\n"; 

    int i = 0, granulation = 50;
    should_define_fun = false;
    while(getline(smt_sat_rel_reader, line)){

        if(should_define_fun){
            proof_file << "(define-fun smt_sat_rel" << smt_sat_rel_num++ << " () Bool\n(and\n";
            should_define_fun = false; 
        }

        proof_file << line << endl;

        if(i == granulation){
            proof_file << ")\n)\n";
            should_define_fun = true;  
            i = 0;
        }

        i++;
    }
    if(i != 1)
        proof_file << ")\n)\n";

    proof_file << "(define-fun smt_sat_rel () Bool\n";
    if(smt_sat_rel_num > 2)
        proof_file << "(and\n";
    for(int i = 1; i < smt_sat_rel_num; i++)
        proof_file << "smt_sat_rel" << i << "\n";
    if(smt_sat_rel_num > 2)
        proof_file << ")\n";
    proof_file << ")\n";


    smt_subspace_reader = ifstream("smt_subspace.smt2");
    if(std::filesystem::file_size("smt_subspace.smt2") > 0)
        proof_file << "(define-fun smt_subspace" << smt_subspace_num++ << " () Bool\n(and\n"; 

    should_define_fun = false;
    while(getline(smt_subspace_reader, line)){

        if(should_define_fun){
            proof_file << "(define-fun smt_subspace" << smt_subspace_num++ << " () Bool\n(and\n";
            should_define_fun = false; 
        }

        if(line == "---"){
            proof_file << ")\n)\n";
            should_define_fun = true;    
        } else
            proof_file << line << endl;
    }

    proof_file << "(define-fun smt_subspace () Bool\n";
    if(smt_subspace_num > 2)
        proof_file << "(and\n";
    for(int i = 1; i < smt_subspace_num; i++)
        proof_file << "smt_subspace" << i << "\n";
    if(smt_subspace_num > 2)
        proof_file << ")\n";
    proof_file << ")\n";

    ifstream sat_subspace_reader = ifstream("sat_subspace.smt2");
    if(std::filesystem::file_size("sat_subspace.smt2") > 0)
        proof_file << "(define-fun sat_subspace" << sat_subspace_num++ << " () Bool\n(and\n"; 

    should_define_fun = false;
    while(getline(sat_subspace_reader, line)){

        if(should_define_fun){
            proof_file << "(define-fun sat_subspace" << sat_subspace_num++ << " () Bool\n(and\n";
            should_define_fun = false; 
        }

        if(line == "---"){
            proof_file << ")\n)\n";
            should_define_fun = true;    
        } else
            proof_file << line << endl;
    }

    proof_file << "(define-fun sat_subspace () Bool\n";
    if(sat_subspace_num > 2)
        proof_file << "(and\n";
    for(int i = 1; i < sat_subspace_num; i++)
        proof_file << "sat_subspace" << i << "\n";
    if(sat_subspace_num > 2)
        proof_file << ")\n";
    proof_file << ")" << endl;

    system("cat sat_smt_funs.smt2 >> proof.smt2");

    system("cat smt_sat_funs.smt2 >> proof.smt2");

    system("mkdir -p proofs");

    for(int i = 1; i < smt_subspace_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check SMT containing " << i << "\")\n";
        proof_file << "(assert (and smt_encode (not smt_subspace" << i << ")))\n";

        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"smt_containing_proof" << i <<".out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }


    for(int i = 1; i < sat_subspace_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check SAT containing " << i << "\")\n";
        proof_file << "(assert (and sat_encode (not sat_subspace" << i << ")))\n";

        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"sat_containing_proof" << i <<".out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }

    for(int i = 1; i < smt_sat_rel_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check left-total R" << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "smt_subspace" << endl;
        system("cat left_total.smt2 >> proof.smt2");
        proof_file << "(not smt_sat_rel" << i << ")\n";
        proof_file << ")\n)\n";
        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"left_total_r" << i << "_proof.out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";
    }

    for(int i = 1; i < sat_subspace_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check left-total " << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "smt_subspace" << endl;
        system("cat left_total.smt2 >> proof.smt2");
        proof_file << "(not sat_subspace" << i << ")\n";
        proof_file << ")\n)\n";
        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"left_total_" << i << "_proof.out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }

    for(int i = 1; i < smt_sat_rel_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check right-total R" << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "sat_subspace" << endl;
        system("cat right_total.smt2 >> proof.smt2");
        proof_file << "(not smt_sat_rel" << i << ")\n";
        proof_file << ")\n)\n";
        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"right_total_r" << i << "_proof.out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";
    }

    for(int i = 1; i < smt_subspace_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check right-total " << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "sat_subspace" << endl;
        system("cat right_total.smt2 >> proof.smt2");
        proof_file << "(not smt_subspace" << i << ")\n";
        proof_file << ")\n)\n";
        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"right_total_" << i << "_proof.out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }

    proof_file << "\n";

    proof_file << "(push)\n";
    proof_file << "(echo \"Check soundness dom\")\n";
    proof_file << "(assert (and\n";
    proof_file << "smt_subspace\n";
    proof_file << "sat_subspace\n";
    proof_file << "smt_sat_rel\n";
    proof_file << "(distinct smt_dom sat_dom)\n";
    proof_file << ")\n";
    proof_file << ")\n";

    proof_file << "(check-sat)\n";
    proof_file << "(set-option :regular-output-channel \"soundness_proof_dom.out\")\n";
    proof_file << "(get-proof)\n";
    proof_file << "(set-option :regular-output-channel \"stdout\")\n";
    proof_file << "(pop)\n\n";

    for(int i = 1; i < next_constraint_num; i++){
        proof_file << "(push)\n";
        proof_file << "(echo \"Check soundness c" << i << "\")\n";
        proof_file << "(assert (and\n";
        proof_file << "           smt_subspace\n";
        proof_file << "           sat_subspace\n";
        proof_file << "           smt_sat_rel\n";
        proof_file << "           (distinct smt_c" << i << " sat_c" << i << ")\n";
        proof_file << "        )\n";
        proof_file << ")\n";

        proof_file << "(check-sat)\n";
        proof_file << "(set-option :regular-output-channel \"soundness_proof_c" << i <<".out\")\n";
        proof_file << "(get-proof)\n";
        proof_file << "(set-option :regular-output-channel \"stdout\")\n";
        proof_file << "(pop)\n\n";

    }


    system("rm -f helper2.smt2 connection_formula.smt2 trivial*.smt2 sat_dom.smt2 *subspace.smt2");
    system("rm -f left_containing.smt2 right_containing.smt2 left_total.smt2 right_total.smt2 sat_constraints.smt2");
    system("rm -f sat_smt_funs.smt2 smt_sat_funs.smt2");
    system("rm -f connection2step.smt2 constraints2step1.smt2 constraints2step2.smt2 domains2step.smt2 smt_step1_funs.smt2");
    system("rm -f left_total_step1.smt2 smt_step1_funs.smt2 smt_subspace_step1.smt2");

    system("mkdir -p proofs");
    system("mkdir -p proofs_step1");
    system("mv proof.smt2 proofs");
    system("mv proof_step1.smt2 proofs_step1");

    proof_file.close();
}

// Runs the specified solver by executing a system call.
// The input in the appropriate format should be in the inputFile, and the output is
// written to the outputFile
void Encoder::run_solver(const string& outputFile) {

    string command = "";
    if(solver_type == MINISAT && file_type == DIMACS)
        command = "minisat formula.cnf " + outputFile + "> /dev/null 2>&1";
    else if(solver_type == CADICAL && file_type == DIMACS)
        command = "cadical -q formula.cnf | cut -c2- > " + outputFile;
    else if(solver_type == GLUCOSE && file_type == DIMACS)
        command = "../scripts/glucose-wrapper formula.cnf " + outputFile + "> /dev/null 2>&1";
    else if(solver_type == Z3 && file_type == SMTLIB)
        command = "z3 formula.smt2 > " + outputFile;
    else if(solver_type == CVC5 && file_type == SMTLIB)
        command = "cvc5 --produce-models -q formula.smt2 > " + outputFile;
    else
        cerr << "Unsupported combination of solver and file type\n";
    
    system(command.c_str());
}

// Reads the solver output, converts it to a human readable format
// and writes the output to cout
void Encoder::read_solver_output(const string& outputFile) {

    if(unsat){
        cout << "UNSAT" << endl;
        return;
    }

    ifstream output(outputFile);
    if (!output.is_open()) {
        cerr << "Cannot open file\n";
        return;
    }

    string sat;
    output >> sat;
    if(sat.find("UNSAT") != sat.npos || sat.find("unsat") != sat.npos){
        cout << "UNSAT" << endl;
        return;
    }

    cout << "SAT\n";

    if(file_type == SMTLIB){
        output.close();

        if(solver_type == CVC5){
            system("grep define-fun model.out "
                    "| sed -E 's/.*x([0-9]+).*Bool (true|false).*/\\1 \\2/'"
                    " | awk '{if($2==\"false\") printf(\"-%s \",$1); else printf(\"%s \",$1);}'"
                    " > model.tmp && mv model.tmp model.out");
        } else if(solver_type == Z3){
            system("awk '/define-fun/{var=$2} /Bool/{getline; val=$1; gsub(/[()]/, \"\", val); "
                    "if(val==\"false\") printf(\"-%s \", substr(var,2)); else printf(\"%s \", substr(var,2));}' "
                    "model.out > model.tmp && mv model.tmp model.out");
        }
        
        output.open(outputFile);
    }

    int curr_lit_num;
    while (output >> curr_lit_num) {

        bool sign = false;
        if(curr_lit_num < 0){
            sign = true;
            curr_lit_num = -curr_lit_num;
        }

        if(num_to_literal.find(curr_lit_num) == num_to_literal.end())
            continue;

        auto l = num_to_literal[curr_lit_num].get();

        if(id_map.find(l->id) == id_map.end())
            continue;

        Variable* curr_var = id_map[l->id];
        BasicVar* curr_basic_var = get<BasicVar*>(*curr_var);
        BasicVarType* curr_basic_var_type = curr_basic_var->type;

        if(holds_alternative<IntRangeVarType*>(*curr_basic_var_type)){
            IntRangeVarType* c = get<IntRangeVarType*>(*curr_basic_var_type);
            int val = l->val;
            if(!sign){
                if(c->right > val)
                    c->right = val;
            } else {
                if(c->left < val + 1)
                    c->left = val + 1;
            }

            if(c->left == c->right){
                curr_basic_var->value = new BasicExpr(new BasicLiteralExpr(c->left));

                id_map.erase(l->id);

                if(curr_basic_var->is_output)
                    cout << *curr_basic_var->name << " = " << c->left << '\n';
            } 
        } else if(holds_alternative<IntSetVarType*>(*curr_basic_var_type)){
            IntSetVarType* c = get<IntSetVarType*>(*curr_basic_var_type);
            int* left = &(*c->elems)[0];
            int* right = &(*c->elems)[c->elems->size() - 1];

            int val = l->val;
            if(!sign){
                if(*right > val)
                    *right = val;
            } else {
                if(*left < val + 1)
                    *left = val + 1;
            }

            if(*left == *right){
                curr_basic_var->value = new BasicExpr(new BasicLiteralExpr(*left));

                id_map.erase(l->id);
                
                if(curr_basic_var->is_output)
                    cout << *curr_basic_var->name << " = " << *left << '\n';
            } 
        } else if(holds_alternative<SetVarType*>(*curr_basic_var_type)){
                if(!sign)
                    set_variable_map[l->id].insert(l->val);
        } else if(holds_alternative<BasicParType>(*curr_basic_var_type)){
            if(get<BasicParType>(*curr_basic_var_type) == BasicParType::BOOL){


                if(!sign){
                    curr_basic_var->value = new BasicExpr(new BasicLiteralExpr(true));
                    if(curr_basic_var->is_output)
                        cout << *curr_basic_var->name << " = true\n"; 
                    
                } else {
                    curr_basic_var->value = new BasicExpr(new BasicLiteralExpr(false));
                    if(curr_basic_var->is_output)                  
                        cout << *curr_basic_var->name << " = false\n";
                } 
                id_map.erase(l->id);                    
            }
        }

    }

    for(auto set_var : set_variable_map){

        if(!(get<BasicVar*>(*id_map[set_var.first])->is_output))
            continue;

        cout << *get<BasicVar*>(*id_map[set_var.first])->name << " = {";
        if(set_var.second.empty()){
            cout << "}\n";
            continue;
        }

        for(auto it = set_var.second.begin(); it != prev(set_var.second.end()); it++){
            cout << *it << ", ";
        }
        
        cout << *prev(set_var.second.end()) << "}\n";
    }


    for(auto array : array_set){
        auto elems = array->value;

        cout << *array->name << " = array1d(1.." << array->value->size() << ",[";

        int i = 0;
        for(auto elem : *elems){
            if(holds_alternative<string*>(*elem)){

                auto var = get<BasicVar*>(*variable_map[*get<string*>(*elem)]);
                auto val = get<BasicLiteralExpr*>(*var->value);

                if(holds_alternative<IntRangeVarType*>(*var->type) || holds_alternative<IntSetVarType*>(*var->type)){
                    cout << get<int>(*val);
                } else if(holds_alternative<BasicParType>(*var->type)){
                    auto type = get<BasicParType>(*var->type);
                    
                    if(type == BasicParType::BOOL){
                        cout << get<bool>(*val);
                    } else {
                        cout << get<int>(*val);
                    }
                }
            } else {
                auto expr = get<BasicLiteralExpr*>(*elem);
                if(holds_alternative<int>(*expr)){
                    cout << get<int>(*expr);
                } else {
                    cout << get<bool>(*expr);
                }    
            }

            if(i++ < (int)elems->size() - 1)
                cout << ", ";
            else    
                cout << "]);\n";
        }
    }

    output.close();
}

// Encodes a parameter of the model 
void Encoder::encode_parameter(Parameter& param, CNF& cnf_clauses) {

    parameter_map[*param.name] = &param;

}

// Encodes a variable based on it's type.
void Encoder::encode_variable(Variable& var, CNF& cnf_clauses) {
    int new_var_id = next_var_id++;

    if (holds_alternative<BasicVar*>(var)) {
        BasicVar* basic_var = get<BasicVar*>(var);
        variable_map[*basic_var->name] = &var; 
        basic_var->id = new_var_id;

        id_map[new_var_id] = variable_map[*basic_var->name];
        
        if(holds_alternative<IntRangeVarType*>(*basic_var->type)){
            IntRangeVarType* t = get<IntRangeVarType*>(*basic_var->type);

            int left = t->left;
            int right = t->right;

            Clause clause1, clause2, curr_clause;
            clause1 = {make_literal(LiteralType::ORDER, new_var_id, false, left - 1)};
            clause2 = {make_literal(LiteralType::ORDER, new_var_id, true, right)};

            cnf_clauses.push_back(clause1);
            cnf_clauses.push_back(clause2);

            if(export_proof){
                sat_dom_clauses.push_back(clause1);
                sat_dom_clauses.push_back(clause2);
            }

            for(int i = left; i <= right; i++){
                curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, false, i - 1));
                curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, true, i));
                cnf_clauses.push_back(curr_clause);

                if(export_proof)
                    sat_dom_clauses.push_back(curr_clause);

                curr_clause.clear();
            }

            if(export_proof){
                isLIA = true;

                trivial_encoding_vars << "(declare-const " << *basic_var->name << " Int)\n";

                string left_string = left < 0 ? ("(- " + to_string(-left) + ")") : to_string(left);
                string right_string = right < 0 ? ("(- " + to_string(-right) + ")") : to_string(right);
                trivial_encoding_domains << "(<= " << left_string << " " << *basic_var->name << " " << right_string
                                         << ")\n";

                smt_subspace << "(<= " << left_string << " " << *basic_var->name << " " << right_string
                                         << ")\n---\n";
                smt_subspace_step1 << "(<= " << left_string << " " << *basic_var->name << " " << right_string
                            << ")\n---\n";
            }

        } else if(holds_alternative<IntSetVarType*>(*basic_var->type)){
            IntSetVarType* t = get<IntSetVarType*>(*basic_var->type);

            vector<int> v = *t->elems;
            int n = v.size();
            int left = v[0], right = v[n-1];

            Clause clause1, clause2, curr_clause;
            clause1 = {make_literal(LiteralType::ORDER, new_var_id, false, left - 1)};
            clause2 = {make_literal(LiteralType::ORDER, new_var_id, true, right)};

            cnf_clauses.push_back(clause1);
            cnf_clauses.push_back(clause2);

            if(export_proof){
                sat_dom_clauses.push_back(clause1);
                sat_dom_clauses.push_back(clause2);
            }
            for(int i = left; i <= right; i++){
                curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, false, i - 1));
                curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, true, i));
                cnf_clauses.push_back(curr_clause);

                if(export_proof)
                    sat_dom_clauses.push_back(curr_clause);

                curr_clause.clear();
            }            

            for(int i = 0; i < n - 1; i++){
                if(v[i+1] - v[i] > 0){
                    curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, true, v[i]));
                    curr_clause.push_back(make_literal(LiteralType::ORDER, new_var_id, false, v[i+1]-1));
                    cnf_clauses.push_back(curr_clause);

                    if(export_proof)
                        sat_dom_clauses.push_back(curr_clause);

                    curr_clause.clear();  
                }              
            }

            if(export_proof){
                isLIA = true;

                trivial_encoding_vars << "(declare-const " << *basic_var->name << " Int)\n";

                if(n > 1)
                    trivial_encoding_domains << "(or\n";
                for(int i = 0; i < n; i++){
                    string num_string = v[i] < 0 ? ("(- " + to_string(-v[i]) + ")") : to_string(v[i]);
                    trivial_encoding_domains << "(= " << *basic_var->name << " " << num_string << ")\n";
                }
                if(n > 1)
                    trivial_encoding_domains << ")";
                trivial_encoding_domains << endl;

                if(n > 1)
                    smt_subspace << "(or\n";
                for(int i = 0; i < n; i++){
                    string num_string = v[i] < 0 ? ("(- " + to_string(-v[i]) + ")") : to_string(v[i]);
                    smt_subspace << "(= " << *basic_var->name << " " << num_string << ")\n";
                }
                if(n > 1)
                    smt_subspace << ")\n";
                smt_subspace << "---" << endl;

                if(n > 1)
                    smt_subspace_step1 << "(or\n";
                for(int i = 0; i < n; i++){
                    string num_string = v[i] < 0 ? ("(- " + to_string(-v[i]) + ")") : to_string(v[i]);
                    smt_subspace_step1 << "(= " << *basic_var->name << " " << num_string << ")\n";
                }
                if(n > 1)
                    smt_subspace_step1 << ")\n";
                smt_subspace_step1 << "---" << endl;
                
            }

        } else if(holds_alternative<SetVarType*>(*basic_var->type)){
            set_variable_map[basic_var->id] = {};

            SetVarType* t = get<SetVarType*>(*basic_var->type);

            vector<int> v = *t->elems;
            for(int elem : v){
                LiteralPtr yes_l = make_literal(LiteralType::SET_ELEM, basic_var->id, true, elem);
                LiteralPtr not_l = make_literal(LiteralType::SET_ELEM, basic_var->id, false, elem);
                cnf_clauses.push_back({move(yes_l), move(not_l)});
            }

            if(export_proof){
                set_vars.push_back(basic_var);

                isBV = true;

                if(bv_left > v[0])
                    bv_left = v[0];

                if(bv_right < v[v.size()-1])
                    bv_right = v[v.size()-1];

                trivial_encoding_vars << "(declare-const " << *basic_var->name << " (_ BitVec \n"; 
            }

        } else if(holds_alternative<BasicParType>(*basic_var->type)){
            if(get<BasicParType>(*basic_var->type) == BasicParType::BOOL){
                Clause clause;
                clause.push_back(make_literal(LiteralType::BOOL_VARIABLE, basic_var->id, true, 0));
                clause.push_back(make_literal(LiteralType::BOOL_VARIABLE, basic_var->id, false, 0));  
                cnf_clauses.push_back(clause);

                if(export_proof){
                    isLIA = true;

                    trivial_encoding_vars << "(declare-const " << *basic_var->name << " Int)\n";
                    trivial_encoding_domains << "(<= 0 " << *basic_var->name << " 1)\n";
                    
                    smt_subspace << "(<= 0 " << *basic_var->name << " 1)\n";
                    smt_subspace << "---" << endl;
                    
                    smt_subspace_step1 << "(<= 0 " << *basic_var->name << " 1)\n";
                    smt_subspace_step1 << "---" << endl;

                    sat_dom_clauses.push_back(clause);
                }
            }
        }
    } else {
        ArrayVar* array_var = get<ArrayVar*>(var);
        variable_map[*array_var->name] = &var;  
        
        if(array_var->is_output)
            array_set.insert(array_var);
    }
}

// Encodes a helper variable for substitutions
BasicVar* Encoder::encode_int_range_helper_variable(const int left, const int right, CNF& cnf_clauses, bool is2step_var) {

    int sub_id = next_var_id++;
    auto var_type = new IntRangeVarType(left, right);
    string* name = new string("sub_" + to_string(sub_id));
    auto int_range_var = new BasicVar(new BasicVarType(var_type), name, true);
    int_range_var->id = sub_id;

    // variable_map[*int_range_var->name] = new Variable(int_range_var);
    // id_map[sub_id] = variable_map[*int_range_var->name];

    helper_vars.push_back(int_range_var);

    Clause clause1, clause2, curr_clause;
    clause1 = {make_literal(LiteralType::ORDER, sub_id, false, left - 1)};
    clause2 = {make_literal(LiteralType::ORDER, sub_id, true, right)};

    cnf_clauses.push_back(clause1);
    cnf_clauses.push_back(clause2);

    if(export_proof){
        sat_dom_clauses.push_back(clause1);
        sat_dom_clauses.push_back(clause2);
    }
    for(int i = left; i <= right; i++){
        curr_clause.push_back(make_literal(LiteralType::ORDER, sub_id, false, i - 1));
        curr_clause.push_back(make_literal(LiteralType::ORDER, sub_id, true, i));

        cnf_clauses.push_back(curr_clause);

        if(export_proof)
            sat_dom_clauses.push_back(curr_clause);

        curr_clause.clear();
    }    

    if(export_proof){
        isLIA = true;

        trivial_encoding_vars << "(declare-const " << *int_range_var->name << " Int)\n";

        
            string left_string = left < 0 ? ("(- " + to_string(-left) + ")") : to_string(left);
            string right_string = right < 0 ? ("(- " + to_string(-right) + ")") : to_string(right);
        
        if(is2step_var){
            domains2step << "(<= " << left_string << " " << *int_range_var->name << " " << right_string
                                        << ")\n";
            smt_subspace << "(<= " << left_string << " " << *int_range_var->name << " " << right_string
                                        << ")\n---\n";
        } else {
            trivial_encoding_domains << "(<= " << left_string << " " << *int_range_var->name << " " << right_string
                                        << ")\n";
            smt_subspace << "(<= " << left_string << " " << *int_range_var->name << " " << right_string
                                        << ")\n";
            smt_subspace << "---" << endl;

            smt_subspace_step1 << "(<= " << left_string << " " << *int_range_var->name << " " << right_string
                                        << ")\n";
            smt_subspace_step1 << "---" << endl;
            
        }
    }

    return int_range_var;
}

// Encodes a bool helper variable 
BasicVar* Encoder::encode_bool_helper_variable(CNF& cnf_clauses) {

    int sub_id = next_var_id++;
    auto var_type = new BasicVarType(BasicParType::BOOL);
    string* name = new string("sub_" + to_string(sub_id));

    auto bool_var = new BasicVar(var_type, name, true);
    bool_var->id = sub_id;
    cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, sub_id, true, 0),
                           make_literal(LiteralType::BOOL_VARIABLE, sub_id, false, 0)});

    helper_vars.push_back(bool_var);

    // id_map[sub_id] = new Variable(bool_var);

    if(export_proof){
        isLIA = true;

        trivial_encoding_vars << "(declare-const " << *bool_var->name << " Int)\n";
        trivial_encoding_domains << "(<= 0 " << *bool_var->name << " 1)\n";

    }

    return bool_var;
}

// Gets the left border of an int variable domain
int get_left(const BasicVar* var){
    if(holds_alternative<IntRangeVarType*>(*var->type))
        return get<IntRangeVarType*>(*var->type)->left;
    else if(holds_alternative<IntSetVarType*>(*var->type))
        return (*get<IntSetVarType*>(*var->type)->elems)[0];
    else 
        return 0;
}

// Gets the right border of an int variable domain
int get_right(const BasicVar* var){
    if(holds_alternative<IntRangeVarType*>(*var->type))
        return get<IntRangeVarType*>(*var->type)->right;
    else if(holds_alternative<IntSetVarType*>(*var->type))
        return (*get<IntSetVarType*>(*var->type)->elems)[get<IntSetVarType*>(*var->type)->elems->size()-1];
    else
        return 1;
}

// Makes a connection between a direct and order encoding of a variable.
// The variable is supposed to already be encoded using the order encoding
void Encoder::encode_direct(const BasicVar& var, CNF& cnf_clauses){
    
    int left = get_left(&var);
    int right = get_right(&var);

    for(int i = left; i <= right; i++){
        LiteralPtr p = make_literal(LiteralType::DIRECT, var.id, true, i);
        LiteralPtr q = make_literal(LiteralType::ORDER, var.id, true, i);
        LiteralPtr r = make_literal(LiteralType::ORDER, var.id, true, i-1);
        LiteralPtr not_p = make_literal(LiteralType::DIRECT, var.id, false, i);
        LiteralPtr not_q = make_literal(LiteralType::ORDER, var.id, false, i);
        LiteralPtr not_r = make_literal(LiteralType::ORDER, var.id, false, i-1);

        Clause new_clause1 = {not_p, q};
        Clause new_clause2 = {not_p, not_r};
        Clause new_clause3 = {p, not_q, r};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);
        cnf_clauses.push_back(new_clause3);

        if(export_proof){
            sat_dom_clauses.push_back(new_clause1);
            sat_dom_clauses.push_back(new_clause2);
            sat_dom_clauses.push_back(new_clause3);            
        }
    }

}

BasicVar* Encoder::encode_param_as_var(Parameter& param, CNF& cnf_clauses){
    
    auto val = param.value;
    auto type = get<BasicParType>(*param.type);
    if(type == BasicParType::INT){
        int int_val = get<int>(*get<BasicLiteralExpr*>(*val));
        return encode_int_range_helper_variable(int_val, int_val, cnf_clauses);
    } else if(type == BasicParType::BOOL){
        bool bool_val = get<bool>(*get<BasicLiteralExpr*>(*val));
        int sub_id = next_var_id++;
        auto var_type = new BasicVarType(BasicParType::BOOL);
        string* name = new string("sub_" + to_string(sub_id));

        auto bool_var = new BasicVar(var_type, name, true);
        bool_var->id = sub_id;
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, sub_id, bool_val ? true : false, 0)});

        if(export_proof){
            isLIA = true;

            trivial_encoding_vars << "(declare-const " << *bool_var->name << " Int)\n";
            trivial_encoding_domains << "(= " << *bool_var->name << " " << (bool_val ? 1 : 0) << ")\n";

            smt_subspace << "(= " << *bool_var->name << " " << (bool_val ? 1 : 0) << ")\n";
            smt_subspace << "---" << endl;
         
            smt_subspace_step1 << "(= " << *bool_var->name << " " << (bool_val ? 1 : 0) << ")\n";
            smt_subspace_step1 << "---" << endl;
        }

        return bool_var;
    } else {
        auto set_vals = get<SetLiteral*>(*get<BasicLiteralExpr*>(*val));
        vector<int>* elems = new vector<int>;
        if(holds_alternative<SetSetLiteral*>(*set_vals))
            elems = get<SetSetLiteral*>(*set_vals)->elems;
        else {
            auto tmp =*get<SetRangeLiteral*>(*set_vals);
            int left = tmp.left;
            int right = tmp.right;
            for(int i = left; i <= right; i++){
                elems->push_back(i);
            }
        }

        int sub_id = next_var_id++;
        auto var_type = new BasicVarType(new SetVarType(elems));
        string* name = new string("sub_" + to_string(sub_id));

        auto set_var = new BasicVar(var_type, name, true);
        set_var->id = sub_id;

        for(auto elem : *elems){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, sub_id, true, elem)});

            if(export_proof)
                sat_dom_clauses.push_back({make_literal(LiteralType::SET_ELEM, sub_id, true, elem)});
        }
        
        if(export_proof){
            set_vars.push_back(set_var);

            isBV = true;

            if(bv_left > (*elems)[0])
                bv_left = (*elems)[0];

            if(bv_right < (*elems)[(*elems).size()-1])
                bv_right = (*elems)[(*elems).size()-1];

            trivial_encoding_vars << "(declare-const " << *set_var->name << " (_ BitVec \n"; 
        }

        return set_var;
    }
    
}

// Gets a variable argument at index ind from constraint constr
BasicVar* Encoder::get_var(Constraint& constr, int ind, CNF& cnf_clauses){
    auto tmp1 = (*constr.args)[ind];
    auto tmp2 = get<BasicExpr*>(*tmp1);
    
    if(holds_alternative<string*>(*tmp2)){
        auto tmp3 = get<string*>(*tmp2);
        
        if(variable_map.find(*tmp3) != variable_map.end())
            return get<BasicVar*>(*variable_map[*tmp3]);
        else{
            auto param = *parameter_map[*tmp3];
            return encode_param_as_var(param, cnf_clauses);
        }
    } else {
        auto type = get<BasicLiteralExpr*>(*tmp2);
        if(holds_alternative<int>(*type)){
            int int_val = get<int>(*type);
            return encode_int_range_helper_variable(int_val, int_val, cnf_clauses);
        } else if(holds_alternative<bool>(*type)){
            bool bool_val = get<bool>(*type);
            int sub_id = next_var_id++;
            auto var_type = new BasicVarType(BasicParType::BOOL);
            string* name = new string("sub_" + to_string(sub_id));

            auto bool_var = new BasicVar(var_type, name, true);
            bool_var->id = sub_id;
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, sub_id, bool_val ? true : false, 0)});

            if(export_proof){
                isLIA = true;

                sat_dom_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, sub_id, bool_val ? true : false, 0)});

                trivial_encoding_vars << "(declare-const " << *bool_var->name << " Int)\n";
                trivial_encoding_domains << "(= " << *bool_var->name << " " << (bool_val ? 1 : 0) << ")\n";

                smt_subspace << "(= " << *bool_var->name << " " << (bool_val ? 1 : 0) << ")\n";
                smt_subspace << "---" << endl;

                smt_subspace_step1 << "(= " << *bool_var->name << " " << (bool_val ? 1 : 0) << ")\n";
                smt_subspace_step1 << "---" << endl;                
            }
        
            return bool_var;
        } else {
            auto set_vals = get<SetLiteral*>(*type);
            vector<int>* elems = new vector<int>;
            if(holds_alternative<SetSetLiteral*>(*set_vals))
                elems = get<SetSetLiteral*>(*set_vals)->elems;
            else {
                auto tmp =*get<SetRangeLiteral*>(*set_vals);
                int left = tmp.left;
                int right = tmp.right;
                for(int i = left; i <= right; i++){
                    elems->push_back(i);
                }
            }

            int sub_id = next_var_id++;
            auto var_type = new BasicVarType(new SetVarType(elems));
            string* name = new string("sub_" + to_string(sub_id));

            auto set_var = new BasicVar(var_type, name, true);
            set_var->id = sub_id;

            for(auto elem : *elems){
                cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, sub_id, true, elem)});

                if(export_proof){
                    sat_dom_clauses.push_back({make_literal(LiteralType::SET_ELEM, sub_id, true, elem)});
                    smt_subspace << "(= ((_ extract " << elem - bv_left << " " << elem - bv_left << ") " 
                                 << *name << ") #b1)\n---\n";   
                }
            }

            if(export_proof){
                set_vars.push_back(set_var);

                isBV = true;


                trivial_encoding_vars << "(declare-const " << *set_var->name << " (_ BitVec \n"; 
            }

            return set_var;
        }
    }

}

// Gets an array argument at index ind from constraint constr
ArrayLiteral* Encoder::get_array(Constraint& constr, int ind){
    auto tmp1 = (*constr.args)[ind];
    if(holds_alternative<BasicExpr*>(*tmp1)){
        auto tmp2 = get<BasicExpr*>(*tmp1);
        auto tmp3 = get<string*>(*tmp2);
        if(variable_map.find(*tmp3) != variable_map.end()){
            auto tmp4 = get<ArrayVar*>(*variable_map[*tmp3]);
            return tmp4->value;
        } else if(parameter_map.find(*tmp3) != parameter_map.end()){
            auto tmp4 = get<ParArrayLiteral*>(*parameter_map[*tmp3]->value);
            auto tmp5 = tmp4->elems;
            ArrayLiteral* a = new ArrayLiteral();
            for(int i = 0; i < (int)tmp5->size(); i++){
                BasicExpr* b = new BasicExpr((*tmp5)[i]);
                a->push_back(b);
            }

            allocated_arrays.push_back(a);
            return a;
        } else {
            cerr << "Variable/parameter not in use\n";
            return nullptr;
        }
    } else {
        return get<ArrayLiteral*>(*tmp1);
    } 

}

// Gets an int parameter argument at index ind from constraint constr
BasicLiteralExpr* Encoder::get_const(Constraint& constr, int ind){
    auto tmp1 = (*constr.args)[ind];
    auto tmp2 = get<BasicExpr*>(*tmp1);
    if(holds_alternative<BasicLiteralExpr*>(*tmp2)){
        auto tmp3 = get<BasicLiteralExpr*>(*tmp2);
        return tmp3;
    } else {
        string name = *get<string*>(*tmp2);
        auto param = parameter_map[name];
        auto val = param->value;
        return get<BasicLiteralExpr*>(*val);
    }

}

// Gets a set element from an array at index ind
SetLiteral* Encoder::get_set_from_array(const ArrayLiteral& a, int ind){
    auto tmp1 = *(a[ind]);
    if(holds_alternative<BasicLiteralExpr*>(tmp1)){
        auto tmp2 = get<BasicLiteralExpr*>(tmp1);
        auto tmp3 = get<SetLiteral*>(*tmp2);
        return tmp3;
    } else {
        string name = *get<string*>(tmp1);
        auto param = parameter_map[name];
        auto val = param->value;
        auto tmp2 = get<BasicLiteralExpr*>(*val);
        auto tmp3 = get<SetLiteral*>(*tmp2);
        return tmp3;
    }
}


// Gets an int element from an array at index ind
int Encoder::get_int_from_array(const ArrayLiteral& a, int ind){
    auto tmp1 = get<BasicLiteralExpr*>(*a[ind]);
    auto tmp2 = get<int>(*tmp1);
    return tmp2;
}

// Gets a bool element from an array at index ind
bool Encoder::get_bool_from_array(const ArrayLiteral& a, int ind){
    auto tmp1 = get<BasicLiteralExpr*>(*a[ind]);
    auto tmp2 = get<bool>(*tmp1);
    return tmp2;
}

// Gets a variable element from an array at index ind
BasicVar* Encoder::get_var_from_array(const ArrayLiteral& a, int ind){

    auto tmp2 = a[ind];
    
    if(holds_alternative<string*>(*tmp2)){
        auto tmp3 = get<string*>(*tmp2);
        
        if(variable_map.find(*tmp3) != variable_map.end())
            return get<BasicVar*>(*variable_map[*tmp3]);
        else{
            auto param = *parameter_map[*tmp3];
            return encode_param_as_var(param, cnf_clauses);
        }
    } else {
        auto type = get<BasicLiteralExpr*>(*tmp2);
        if(holds_alternative<int>(*type)){
            int int_val = get<int>(*type);
            return encode_int_range_helper_variable(int_val, int_val, cnf_clauses);
        } else if(holds_alternative<bool>(*type)){
            bool bool_val = get<bool>(*type);
            int sub_id = next_var_id++;
            auto var_type = new BasicVarType(BasicParType::BOOL);
            string* name = new string("sub_" + to_string(sub_id));

            auto bool_var = new BasicVar(var_type, name, true);
            bool_var->id = sub_id;
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, sub_id, bool_val ? true : false, 0)});

            if(export_proof){
                isLIA = true;

                trivial_encoding_vars << "(declare-const " << *bool_var->name << " Int)\n";
                trivial_encoding_domains << "(= " << *bool_var->name << " " << (bool_val ? 1 : 0) << ")\n";

                smt_subspace << "(= " << *bool_var->name << " " << (bool_val ? 1 : 0) << ")\n";
                smt_subspace << "---" << endl;
                
                smt_subspace_step1 << "(= " << *bool_var->name << " " << (bool_val ? 1 : 0) << ")\n";
                smt_subspace_step1 << "---" << endl;
            }
        
            return bool_var;
        } else {
            auto set_vals = get<SetLiteral*>(*type);
            vector<int>* elems = new vector<int>;
            if(holds_alternative<SetSetLiteral*>(*set_vals))
                elems = get<SetSetLiteral*>(*set_vals)->elems;
            else {
                auto tmp =*get<SetRangeLiteral*>(*set_vals);
                int left = tmp.left;
                int right = tmp.right;
                for(int i = left; i <= right; i++){
                    elems->push_back(i);
                }
            }

            int sub_id = next_var_id++;
            auto var_type = new BasicVarType(new SetVarType(elems));
            string* name = new string("sub_" + to_string(sub_id));

            auto set_var = new BasicVar(var_type, name, true);
            set_var->id = sub_id;

            for(auto elem : *elems){
                cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, sub_id, true, elem)});

                if(export_proof)
                    sat_dom_clauses.push_back({make_literal(LiteralType::SET_ELEM, sub_id, true, elem)});
            }

            if(export_proof){
                set_vars.push_back(set_var);

                isBV = true;

                if(bv_left > (*elems)[0])
                    bv_left = (*elems)[0];

                if(bv_right < (*elems)[(*elems).size()-1])
                    bv_right = (*elems)[(*elems).size()-1];

                trivial_encoding_vars << "(declare-const " << *set_var->name << " (_ BitVec \n"; 
            }            

            return set_var;
        }
    }
}

// Gets the elements of a set variable
vector<int>* Encoder::get_set_elems(const BasicVar& var){
    return get<SetVarType*>(*var.type)->elems;
}


// Checks which constraint is in question and calls the
// appropriate function to encode it
void Encoder::encode_constraint(Constraint& constr, CNF& cnf_clauses) {
    
    
    if(*constr.name == "array_int_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_int_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "array_int_maximum"){
        auto m = get_var(constr, 0, cnf_clauses);
        auto x = get_array(constr, 1);
        encode_array_int_maximum(*m, *x, cnf_clauses);
    } else if(*constr.name == "array_int_minimum"){
        auto m = get_var(constr, 0, cnf_clauses);
        auto x = get_array(constr, 1);
        encode_array_int_minimum(*m, *x, cnf_clauses);
    } else if(*constr.name == "array_var_int_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_var_int_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "int_abs"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_int_abs(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_div"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_div(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_eq"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_int_eq(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_eq_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_eq_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_eq_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_eq_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_le"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_int_le(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_le_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_le_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_le_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_le_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_eq"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_int_lin_eq(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "int_lin_eq_reif"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_eq_reif(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_eq_imp"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_eq_imp(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_le"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_int_lin_le(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "int_lin_le_reif"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_le_reif(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_le_imp"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_le_imp(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_ne"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_int_lin_ne(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "int_lin_ne_reif"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_ne_reif(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lin_ne_imp"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        auto r = get_var(constr, 3, cnf_clauses);
        encode_int_lin_ne_imp(*a, *b, c, *r, cnf_clauses);
    } else if(*constr.name == "int_lt"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_int_lt(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_lt_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_lt_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_lt_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_lt_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_max"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_max(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_min"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_min(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_mod"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_mod(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_ne"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_int_ne(*a, *b, cnf_clauses);
    } else if(*constr.name == "int_ne_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_ne_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_ne_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_int_ne_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "int_plus"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_plus(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_pow"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_pow(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "int_times"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_int_times(*a, *b, *c, cnf_clauses);
    } else if(*constr.name == "array_bool_and"){
        auto as = get_array(constr, 0);
        auto r = get_var(constr, 1, cnf_clauses);
        encode_array_bool_and(*as, *r, cnf_clauses);
    } else if(*constr.name == "array_bool_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_bool_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "array_bool_or"){
        auto as = get_array(constr, 0);
        auto r = get_var(constr, 1, cnf_clauses);
        encode_array_bool_or(*as, *r, cnf_clauses);
    } else if(*constr.name == "array_bool_xor"){
        auto as = get_array(constr, 0);
        encode_array_bool_xor(*as, cnf_clauses);
    } else if(*constr.name == "array_var_bool_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_var_bool_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "bool2int"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_bool2int(*a, *b, cnf_clauses);
    } else if(*constr.name == "bool_and"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_and(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_clause"){
        auto as = get_array(constr, 0);
        auto bs = get_array(constr, 1);
        encode_bool_clause(*as, *bs, cnf_clauses);
    } else if(*constr.name == "bool_eq"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_bool_eq(*a, *b, cnf_clauses);
    } else if(*constr.name == "bool_eq_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_eq_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_eq_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_eq_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_le"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_bool_le(*a, *b, cnf_clauses);
    } else if(*constr.name == "bool_le_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_le_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_le_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_le_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_lin_eq"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_bool_lin_eq(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "bool_lin_le"){
        auto a = get_array(constr, 0);
        auto b = get_array(constr, 1);
        auto c = get<int>(*get_const(constr, 2));
        encode_bool_lin_le(*a, *b, c, cnf_clauses);
    } else if(*constr.name == "bool_lt"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_bool_lt(*a, *b, cnf_clauses);
    } else if(*constr.name == "bool_lt_reif"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_lt_reif(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_lt_imp"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_lt_imp(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_not"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        encode_bool_not(*a, *b, cnf_clauses);
    } else if(*constr.name == "bool_or"){
        auto a = get_var(constr, 0, cnf_clauses);
        auto b = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_bool_or(*a, *b, *r, cnf_clauses);
    } else if(*constr.name == "bool_xor"){
        if(constr.args->size() == 3){
            auto a = get_var(constr, 0, cnf_clauses);
            auto b = get_var(constr, 1, cnf_clauses);
            auto r = get_var(constr, 2, cnf_clauses);
            encode_bool_xor(*a, *b, *r, cnf_clauses);
        } else {
            auto a = get_var(constr, 0, cnf_clauses);
            auto b = get_var(constr, 1, cnf_clauses);
            encode_bool_xor(*a, *b, cnf_clauses);            
        }
    } else if(*constr.name == "array_set_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_set_element(*b, *as, *c, cnf_clauses);
    }  else if(*constr.name == "array_var_set_element"){
        auto b = get_var(constr, 0, cnf_clauses);
        auto as = get_array(constr, 1);
        auto c = get_var(constr, 2, cnf_clauses);
        encode_array_var_set_element(*b, *as, *c, cnf_clauses);
    } else if(*constr.name == "set_card"){
        auto S = get_var(constr, 0, cnf_clauses);
        auto x = get_var(constr, 1, cnf_clauses);
        encode_set_card(*S, *x, cnf_clauses);
    } else if(*constr.name == "set_diff"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_diff(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_eq"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_eq(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_eq_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_eq_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_eq_imp"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_eq_imp(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_in"){
        auto tmp1 = (*constr.args)[1];
        auto tmp2 = get<BasicExpr*>(*tmp1);
        if(holds_alternative<string*>(*tmp2)){
            if(variable_map.find(*get<string*>(*tmp2)) != variable_map.end()){
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_var(constr, 1, cnf_clauses);
                encode_set_in(*x, *S, cnf_clauses);
            } else {
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_const(constr, 1);
                encode_set_in(*x, *S, cnf_clauses);                
            }
        } else {
            auto x = get_var(constr, 0, cnf_clauses);
            auto S = get_const(constr, 1);
            encode_set_in(*x, *S, cnf_clauses);            
        }
    } else if(*constr.name == "set_in_reif"){
        auto tmp1 = (*constr.args)[1];
        auto tmp2 = get<BasicExpr*>(*tmp1);
        if(holds_alternative<string*>(*tmp2)){
            if(variable_map.find(*get<string*>(*tmp2)) != variable_map.end()){
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_var(constr, 1, cnf_clauses);
                auto r = get_var(constr, 2, cnf_clauses);
                encode_set_in_reif(*x, *S, *r, cnf_clauses);
            } else {
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_const(constr, 1);
                auto r = get_var(constr, 2, cnf_clauses);
                encode_set_in_reif(*x, *S, *r, cnf_clauses);                
            }
        } else {
            auto x = get_var(constr, 0, cnf_clauses);
            auto S = get_const(constr, 1);
            auto r = get_var(constr, 2, cnf_clauses);
            encode_set_in_reif(*x, *S, *r, cnf_clauses);            
        }
    } else if(*constr.name == "set_in_imp"){
        auto tmp1 = (*constr.args)[1];
        auto tmp2 = get<BasicExpr*>(*tmp1);
        if(holds_alternative<string*>(*tmp2)){
            if(variable_map.find(*get<string*>(*tmp2)) != variable_map.end()){
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_var(constr, 1, cnf_clauses);
                auto r = get_var(constr, 2, cnf_clauses);
                encode_set_in_imp(*x, *S, *r, cnf_clauses);
            } else {
                auto x = get_var(constr, 0, cnf_clauses);
                auto S = get_const(constr, 1);
                auto r = get_var(constr, 2, cnf_clauses);
                encode_set_in_imp(*x, *S, *r, cnf_clauses);                
            }
        } else {
            auto x = get_var(constr, 0, cnf_clauses);
            auto S = get_const(constr, 1);
            auto r = get_var(constr, 2, cnf_clauses);
            encode_set_in_imp(*x, *S, *r, cnf_clauses);            
        }
    } else if(*constr.name == "set_ne"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_ne(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_ne_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_ne_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_ne_imp"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_ne_imp(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_intersect"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_intersect(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_le"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_le(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_le_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_le_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_le_imp"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_le_imp(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_lt"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_lt(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_lt_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_lt_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_lt_imp"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_lt_imp(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_subset"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_subset(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_subset_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_subset_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_subset_imp"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_subset_imp(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_superset"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        encode_set_superset(*x, *y, cnf_clauses);
    } else if(*constr.name == "set_superset_reif"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_superset_reif(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_superset_imp"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_superset_imp(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_symdiff"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_symdiff(*x, *y, *r, cnf_clauses);
    } else if(*constr.name == "set_union"){
        auto x = get_var(constr, 0, cnf_clauses);
        auto y = get_var(constr, 1, cnf_clauses);
        auto r = get_var(constr, 2, cnf_clauses);
        encode_set_union(*x, *y, *r, cnf_clauses);
    }      

    // if(!helper_vars.empty())
    //     cleanup_helper_variables();
    if(!allocated_arrays.empty())
        cleanup_arrays();

    if(file_type == DIMACS)
        write_clauses_to_dimacs_file(cnf_clauses);
    else if(file_type == SMTLIB)
        write_clauses_to_smtlib_file(cnf_clauses);

    if(export_proof){
        if(file_type != SMTLIB)
            write_clauses_to_smtlib_file(cnf_clauses);
        write_sat_constraint_clauses();
        write_sat_dom_clauses();
        write_definition_clauses();
    }
}

// ---------------------------- Encoding Int constraints -------------------------------------

// Primitive comparison of type: a - b <= c
bool Encoder::encode_primitive_comparison_minus(const BasicVar& a, const BasicVar& b, int c, CNF& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);

    if(c < a_left - b_right)
        return false; 

    Clause curr_clause;
    for(int i = a_left - 1; i <= a_right; i++){
        for(int j = -b_right - 1; j <= -b_left; j++)
            if(i + j == c-1){
                curr_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, i));
                curr_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, -j - 1));
                cnf_clauses.push_back(curr_clause);

                if(export_proof)
                    sat_constraint_clauses.push_back(curr_clause);

                curr_clause.clear();
            }

    }

    return true;
}

// Primitive comparison of type: a + b <= c
bool Encoder::encode_primitive_comparison_plus(const BasicVar& a, const BasicVar& b, int c, CNF& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);

    if(c < a_left + b_left)
        return false;

    Clause curr_clause;
    for(int i = a_left - 1; i <= a_right; i++){
        for(int j = b_left - 1; j <= b_right; j++){
            if(i + j == c-1){
                curr_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, i));
                curr_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, j));
                cnf_clauses.push_back(curr_clause);

                if(export_proof)
                    sat_constraint_clauses.push_back(curr_clause);

                curr_clause.clear();
            }
        }
    }

    return true;
}

// Reifies the temp_clauses to be equivalent to the boolean variable r
void Encoder::reify(CNF& temp_clauses, const BasicVar& r, CNF& cnf_clauses){
    
    Clause helpers;

    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

    for(auto c : temp_clauses){
        LiteralPtr helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        for(auto lit : c){
            Clause new_clause;
            new_clause.push_back(make_literal(lit->type, lit->id, lit->pol ? false : true, lit->val));
            
            if(export_proof)
                helper_map[helper->id].push_back(new_clause);
            
            new_clause.push_back(helper);

            cnf_clauses.push_back(new_clause);

            if(export_proof)
                sat_constraint_clauses.push_back(new_clause);
        }
        helpers.push_back(make_literal(LiteralType::HELPER, helper->id, true, 0));
    }

    LiteralPtr not_top_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

    if(export_proof)
        helper_map[not_top_helper->id].push_back(helpers);

    helpers.push_back(not_top_helper);
    cnf_clauses.push_back(helpers);
    if(export_proof)
        sat_constraint_clauses.push_back(helpers);

    LiteralPtr top_helper = make_literal(LiteralType::HELPER, not_top_helper->id, true, 0);

    if(export_proof){
        helper_map[top_helper->id].push_back({not_r});
    }

    cnf_clauses.push_back({not_top_helper, not_r});
    if(export_proof){
        sat_constraint_clauses.push_back({not_top_helper, not_r});
    }

    LiteralPtr not_topmost_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    for(auto c : temp_clauses){

        if(export_proof)
            helper_map[not_topmost_helper2->id].push_back(c);

        c.push_back(not_topmost_helper2);
        cnf_clauses.push_back(c);
        if(export_proof)
            sat_constraint_clauses.push_back(c);
    }

    
    if(export_proof)
        helper_map[not_topmost_helper2->id].push_back({yes_r});

    cnf_clauses.push_back({yes_r, not_topmost_helper2});
    if(export_proof)
        sat_constraint_clauses.push_back({yes_r, not_topmost_helper2});

    LiteralPtr topmost_helper2 = make_literal(LiteralType::HELPER, not_topmost_helper2->id, true, 0);
    cnf_clauses.push_back({top_helper, topmost_helper2});

    if(export_proof){
        definition_clauses.push_back({top_helper, topmost_helper2});
        sat_constraint_clauses.push_back({top_helper, topmost_helper2});
    }
}

// Reifies the temp_clauses to be equivalent to the helper variable r
void Encoder::reify_helper(CNF& temp_clauses, const LiteralPtr& r, CNF& cnf_clauses){
    
    Clause helpers;

    LiteralPtr not_r = make_literal(LiteralType::HELPER, r->id, false, 0);
    LiteralPtr yes_r = make_literal(LiteralType::HELPER, r->id, true, 0);

    for(auto c : temp_clauses){
        LiteralPtr helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        for(auto lit : c){
            Clause new_clause;
            new_clause.push_back(make_literal(lit->type, lit->id, lit->pol ? false : true, lit->val));
            
            if(export_proof)
                helper_map[helper->id].push_back(new_clause);
            
            new_clause.push_back(helper);

            cnf_clauses.push_back(new_clause);

            if(export_proof)
                sat_constraint_clauses.push_back(new_clause);
        }
        helpers.push_back(make_literal(LiteralType::HELPER, helper->id, true, 0));
    }

    if(export_proof)
        helper_map[-yes_r->id].push_back(helpers);

    helpers.push_back(yes_r);
    cnf_clauses.push_back(helpers);
    if(export_proof)
        sat_constraint_clauses.push_back(helpers);


    for(auto c : temp_clauses){

        if(export_proof)
            helper_map[not_r->id].push_back(c);

        c.push_back(not_r);
        cnf_clauses.push_back(c);
        if(export_proof)
            sat_constraint_clauses.push_back(c);
    }

}

// Impifies the temp_clauses to be implied by the boolean variable r
void Encoder::impify(CNF& temp_clauses, const BasicVar& r, CNF& cnf_clauses){
    
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    for(auto clause : temp_clauses){

        clause.push_back(not_r);
        cnf_clauses.push_back(clause);

        if(export_proof){
            sat_constraint_clauses.push_back(clause);

            bool is_definition = false;
            for(auto l : clause)
                if(l->type == LiteralType::HELPER){
                    is_definition = true;
                    break;
                }

            if(is_definition)
                definition_clauses.push_back(clause);
        }
    }
}

// Encodes a constraint of type as[b] = c, where as is an array of int parameters
void Encoder::encode_array_int_element(const BasicVar& b, const ArrayLiteral& as, BasicVar& c, CNF& cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(and\n";
        trivial_encoding_constraints << "(<= 1 " << *b.name << " " << as.size() << ")\n";
        trivial_encoding_constraints << "(= " << *c.name << "\n";
        for(int i = 0; i < (int)as.size(); i++){
            auto elem = get_int_from_array(as, i);
            string elem_string = (elem < 0) ? "(" + to_string(-elem) + ")" : to_string(elem);
            trivial_encoding_constraints << "(ite (= " << *b.name << " " << i + 1 << ") " << elem_string << "\n";
        }
        int left = get_left(&c);
        string left_string = (left < 0) ? "(" + to_string(-left) + ")" : to_string(left);
        trivial_encoding_constraints << left_string << endl;
        for(int i = 0; i < (int)as.size() + 2; i++)
            trivial_encoding_constraints << ")";
        
        trivial_encoding_constraints << ")\n";
        
    }

    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    Clause helpers;  
    Clause new_clause1, new_clause2;
    for(int i = b_left; i <= b_right; i++){
        if(i < 1 || i > (int)as.size())
            continue;
        
        LiteralPtr helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        new_clause1 = { make_literal(LiteralType::ORDER, b.id, true, i), helper};
        new_clause2 = { make_literal(LiteralType::ORDER, b.id, false, i-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);

        if(export_proof){
            helper_map[helper->id].push_back({make_literal(LiteralType::ORDER, b.id, true, i)});
            helper_map[helper->id].push_back({make_literal(LiteralType::ORDER, b.id, false, i-1)});

            sat_constraint_clauses.push_back(new_clause1);
            sat_constraint_clauses.push_back(new_clause2);
        }

        int curr_elem = get_int_from_array(as, i-1);
        if(c_left > curr_elem || c_right < curr_elem){
            continue;
        }

        new_clause1 = { make_literal(LiteralType::ORDER, c.id, true, curr_elem), helper};
        new_clause2 = { make_literal(LiteralType::ORDER, c.id, false, curr_elem-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);
        
        if(export_proof){
            helper_map[helper->id].push_back({make_literal(LiteralType::ORDER, c.id, true, curr_elem)});
            helper_map[helper->id].push_back({make_literal(LiteralType::ORDER, c.id, false, curr_elem-1)});

            sat_constraint_clauses.push_back(new_clause1);
            sat_constraint_clauses.push_back(new_clause2);
        }

        LiteralPtr not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }
    
    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }

}


// Encodes a constraint of type m = max(x1, x2, ... xn)
void Encoder::encode_array_int_maximum(const BasicVar& m, const ArrayLiteral& x, CNF& cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        if(x.size() > 1)
            trivial_encoding_constraints << "(and ";
        trivial_encoding_constraints << "(and ";
        for(int i = 0; i < (int)x.size(); i++){
            auto var = get_var_from_array(x, i);
            trivial_encoding_constraints << "(>= " << *m.name << " " << *var->name << ")\n";
        }
        if(x.size() > 1)
            trivial_encoding_constraints << ")";

        if(x.size() > 1)
            trivial_encoding_constraints << "(or ";
        for(int i = 0; i < (int)x.size(); i++){
            auto var = get_var_from_array(x, i);
            trivial_encoding_constraints << "(= " << *m.name << " " << *var->name << ")\n";
        }
        if(x.size() > 1)
            trivial_encoding_constraints << ")";
        trivial_encoding_constraints << ")\n)\n";
    }


    CNF temp_clauses;
    Clause helpers;
    bool found = false;
    for(int i = 0; i < (int)x.size(); i++){

        auto curr_var = get_var_from_array(x, i);
        bool ret_val;

        if(export_proof){
            export_proof = false;
            ret_val = encode_primitive_comparison_minus(m, *curr_var, 0, temp_clauses);
            export_proof = true;
        } else {
            ret_val = encode_primitive_comparison_minus(m, *curr_var, 0, temp_clauses);
        }

        if(ret_val){
            found = true;

            LiteralPtr helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
            for(auto c : temp_clauses){

                if(export_proof)
                    helper_map[helper->id].push_back(c);

                c.push_back(helper);
                cnf_clauses.push_back(c);

                if(export_proof)
                    sat_constraint_clauses.push_back(c);
            }

            LiteralPtr not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
            helpers.push_back(not_helper);
        }

        if(!encode_primitive_comparison_minus(*curr_var, m, 0, cnf_clauses)){
            declare_unsat(cnf_clauses);
            return;
        }

        temp_clauses.clear();
    }

    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }

    if(!found)
        declare_unsat(cnf_clauses); 
}

// Encodes a constraint of type m = min(x1, x2, ... xn)
void Encoder::encode_array_int_minimum(const BasicVar& m, const ArrayLiteral& x, CNF& cnf_clauses){

        if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        if(x.size() > 1)
            trivial_encoding_constraints << "(and ";
        trivial_encoding_constraints << "(and ";
        for(int i = 0; i < (int)x.size(); i++){
            auto var = get_var_from_array(x, i);
            trivial_encoding_constraints << "(<= " << *m.name << " " << *var->name << ")\n";
        }
        if(x.size() > 1)
            trivial_encoding_constraints << ")";

        if(x.size() > 1)
            trivial_encoding_constraints << "(or ";
        for(int i = 0; i < (int)x.size(); i++){
            auto var = get_var_from_array(x, i);
            trivial_encoding_constraints << "(= " << *m.name << " " << *var->name << ")\n";
        }
        if(x.size() > 1)
            trivial_encoding_constraints << ")";
        trivial_encoding_constraints << ")\n)\n";
    }

    CNF temp_clauses;
    Clause helpers;
    bool found = false;
    for(int i = 0; i < (int)x.size(); i++){

        auto curr_var = get_var_from_array(x, i);
        bool ret_val;

        if(export_proof){
            export_proof = false;
            ret_val = encode_primitive_comparison_minus(*curr_var, m, 0, temp_clauses);
            export_proof = true;
        } else {
            ret_val = encode_primitive_comparison_minus(*curr_var, m, 0, temp_clauses);
        }

        if(ret_val){
            found = true;

            LiteralPtr helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
            for(auto c : temp_clauses){

                if(export_proof)
                    helper_map[helper->id].push_back(c);

                c.push_back(helper);
                cnf_clauses.push_back(c);

                if(export_proof)
                    sat_constraint_clauses.push_back(c);
            }

            LiteralPtr not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
            helpers.push_back(not_helper);
        }

        if(!encode_primitive_comparison_minus(m, *curr_var, 0, cnf_clauses)){
            declare_unsat(cnf_clauses);
            return;
        }

        temp_clauses.clear();
    }

    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }

    if(!found)
        declare_unsat(cnf_clauses);    

}

// TODO ispravi da se poziv int_eq ne kodira za proof
// Encodes a constraint of type as[b] = c, where as is an array of int variables
void Encoder::encode_array_var_int_element(const BasicVar& b, const ArrayLiteral& as, BasicVar& c, CNF& cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(and\n";
        trivial_encoding_constraints << "(<= 1 " << *b.name << " " << as.size() << ")\n";
        trivial_encoding_constraints << "(= " << *c.name << "\n";
        for(int i = 0; i < (int)as.size(); i++){
            auto var = get_var_from_array(as, i);
            trivial_encoding_constraints << "(ite (= " << *b.name << " " << i + 1 << ") " << *var->name << "\n";
        }
        int left = get_left(&c);
        string left_string = (left < 0) ? "(" + to_string(-left) + ")" : to_string(left);
        trivial_encoding_constraints << left_string << endl;
        for(int i = 0; i < (int)as.size() + 2; i++)
            trivial_encoding_constraints << ")";
        
        trivial_encoding_constraints << ")\n";
    }

    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    Clause helpers;
    CNF temp_clauses;   
    Clause new_clause1, new_clause2;
    for(int i = b_left; i <= b_right; i++){
        if(i < 1 || i > (int)as.size())
            continue;
        
        LiteralPtr helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        new_clause1 = { make_literal(LiteralType::ORDER, b.id, true, i), helper};
        new_clause2 = { make_literal(LiteralType::ORDER, b.id, false, i-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);

        if(export_proof){
            helper_map[helper->id].push_back({make_literal(LiteralType::ORDER, b.id, true, i)});
            helper_map[helper->id].push_back({make_literal(LiteralType::ORDER, b.id, false, i-1)});

            sat_constraint_clauses.push_back(new_clause1);
            sat_constraint_clauses.push_back(new_clause2);
        }

        auto curr_elem = get_var_from_array(as, i-1);

        if(c_left > get_right(curr_elem) || c_right < get_left(curr_elem)){
            continue;
        }

        if(export_proof){
            export_proof = false;
            encode_int_eq(c, *curr_elem, temp_clauses);
            export_proof = true;
        } else 
            encode_int_eq(c, *curr_elem, temp_clauses);

        for(auto c : temp_clauses){
            if(export_proof)
                helper_map[helper->id].push_back(c);

            c.push_back(helper);
            cnf_clauses.push_back(c);

            if(export_proof){
                sat_constraint_clauses.push_back(c);
            }
        }   

        LiteralPtr not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);

        temp_clauses.clear();
    }
    
    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }

}



// Encodes a constraint of type |a| = b
void Encoder::encode_int_abs(const BasicVar& a, const BasicVar& b, CNF& cnf_clauses){
    
    if(export_proof){
        
        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *b.name << " (ite (>= " <<
                                     *a.name << " 0) " << *a.name << " (- " << *a.name <<
                                    ")))\n)\n";
    }


    int b_left = get_left(&b);
    int b_right = get_right(&b);
    if(b_left < 0){
        if(b_right < 0){
            declare_unsat(cnf_clauses);
            return;
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1)});
            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1)});
        }
    }

    Clause temp_clause;

    CNF new_clauses1;

    bool ret_val1, ret_val2;
    if(export_proof){
        export_proof = false;
        ret_val1 = encode_primitive_comparison_minus(a, b, 0, new_clauses1);
        ret_val2 = encode_primitive_comparison_minus(b, a, 0, new_clauses1);
        export_proof = true;
    } else {
        ret_val1 = encode_primitive_comparison_minus(a, b, 0, new_clauses1);
        ret_val2 = encode_primitive_comparison_minus(b, a, 0, new_clauses1);       
    }

    if(ret_val1 && ret_val2){
        int id1 = next_helper_id++;
        LiteralPtr helper1 = make_literal(LiteralType::HELPER, id1, true, 0);
        temp_clause.push_back(helper1);

        for(int i = 0; i < (int)new_clauses1.size(); i++){
            if(export_proof)
                helper_map[id1].push_back(new_clauses1[i]);

            new_clauses1[i].push_back(make_literal(LiteralType::HELPER, id1, false, 0));

            cnf_clauses.push_back(new_clauses1[i]);

            if(export_proof)
                sat_constraint_clauses.push_back(new_clauses1[i]);
        }
    }
        

    CNF new_clauses2;    
    if(export_proof){
        export_proof = false;
        encode_primitive_comparison_plus(b, a, 0, new_clauses2);
        export_proof = true;
    } else 
        encode_primitive_comparison_plus(b, a, 0, new_clauses2);

    int id2 = next_helper_id++;
    LiteralPtr helper2 = make_literal(LiteralType::HELPER, id2, true, 0);
    if(!new_clauses2.empty()){

        temp_clause.push_back(helper2);
        for(int i = 0; i < (int)new_clauses2.size(); i++){
            if(export_proof)
                helper_map[id2].push_back(new_clauses2[i]);

            new_clauses2[i].push_back(make_literal(LiteralType::HELPER, id2, false, 0));

            cnf_clauses.push_back(new_clauses2[i]);

            if(export_proof)
                sat_constraint_clauses.push_back(new_clauses2[i]);
        }
    }
    
    CNF temp_clauses;
    if(export_proof){
        export_proof = false;
        encode_primitive_comparison_plus(a, b, -1, temp_clauses);
        export_proof = true;
    } else 
        encode_primitive_comparison_plus(a, b, -1, temp_clauses);

    if(!temp_clauses.empty()){
        temp_clause.push_back(helper2);

        Clause helpers;
        Clause new_clause;
        LiteralPtr helper;
        for(auto c : temp_clauses){
            int id = next_helper_id++;
            helper = make_literal(LiteralType::HELPER, id, true, 0);
            for(auto lit : c){
                new_clause.push_back(make_literal(LiteralType::ORDER, lit->id, lit->pol ? false : true, lit->val));

                if(export_proof)
                    helper_map[id].push_back(new_clause);

                new_clause.push_back(make_literal(LiteralType::HELPER, id, false, 0));

                cnf_clauses.push_back(new_clause);

                if(export_proof)
                    sat_constraint_clauses.push_back(new_clause);

                new_clause.clear();
            }
            helpers.push_back(helper);

        }

        if(export_proof)
            helper_map[id2].push_back(helpers);

        helpers.push_back(make_literal(LiteralType::HELPER, id2, false, 0));
        cnf_clauses.push_back(helpers);

        if(export_proof)
            sat_constraint_clauses.push_back(helpers);
    }

    if(temp_clause.size() > 1 && temp_clause[temp_clause.size()-1] == temp_clause[temp_clause.size() - 2])
        temp_clause.pop_back();

    cnf_clauses.push_back(temp_clause);
    if(export_proof){
        definition_clauses.push_back(temp_clause);
        sat_constraint_clauses.push_back(temp_clause);
    }

}

// TODO razmisli jel ovo radi za proof export 
// Encodes a constraint of type a / b = c
void Encoder::encode_int_div(const BasicVar& a, const BasicVar& b, const BasicVar& c, CNF& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    if(b_left == 0 && b_right == 0){
        if(export_proof){
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n false\n)\n";
        }

        declare_unsat(cnf_clauses);
        return;
    }

    if(b_left <= 0 && b_right >= 0){
        LiteralPtr l1 = make_literal(LiteralType::ORDER, b.id, true, -1);
        LiteralPtr l2 = make_literal(LiteralType::ORDER, b.id, false, 0);
        cnf_clauses.push_back({l1, l2});

        if(export_proof){
            sat_constraint_clauses.push_back({l1, l2});
        }
    }

    if(b_left == 0)
        b_left = 1;
    else if(b_right == 0)
        b_right = -1;


    int bc_left = min({b_left*c_left, b_left*c_right, b_right*c_left, b_right*c_right});
    int bc_right = max({b_left*c_left, b_left*c_right, b_right*c_left, b_right*c_right});
    BasicVar* bc = encode_int_range_helper_variable(bc_left, bc_right, cnf_clauses);
    
    if(export_proof){
        CNF temp_clauses;
        export_proof = false;
        encode_int_times(b, c, *bc, temp_clauses);
        for(auto c : temp_clauses){
            sat_constraint_clauses.push_back(c);
            cnf_clauses.push_back(c);
        }
        export_proof = true;
    } else 
        encode_int_times(b, c, *bc, cnf_clauses);


    int r_left = -(max(abs(b_left), abs(b_right))) + 1;
    int r_right = (max(abs(b_left), abs(b_right))) - 1;
    BasicVar* r = encode_int_range_helper_variable(r_left, r_right, cnf_clauses);


    int r_abs_left = r_left*r_right < 0 ? 0 : min(abs(r_left), abs(r_right));
    int r_abs_right = max(abs(r_left), abs(r_right));
    BasicVar* r_abs = encode_int_range_helper_variable(r_abs_left, r_abs_right, cnf_clauses);

    int b_abs_left = b_left*b_right < 0 ? 0 : min(abs(b_left), abs(b_right));
    int b_abs_right = max(abs(b_left), abs(b_right));
    BasicVar* b_abs = encode_int_range_helper_variable(b_abs_left, b_abs_right, cnf_clauses);

    if(export_proof){
        export_proof = false;

        CNF temp_clauses;
        encode_int_abs(*r, *r_abs, temp_clauses);
        encode_int_abs(b, *b_abs, temp_clauses);
        encode_int_lt(*r_abs, *b_abs, temp_clauses);
        encode_int_plus(*bc, *r, a, temp_clauses);
        export_proof = true;

        for(auto& clause : temp_clauses){
            cnf_clauses.push_back(clause);

            if(export_proof){
                Clause new_clause;
                bool is_definition = true;
                int lit_id = -1;
                for(auto& lit : clause){
                    if(lit->type != LiteralType::HELPER){
                        is_definition = false;
                        new_clause.push_back(lit);
                    } else
                        lit_id = lit->id;
                }

                if(is_definition)
                    definition_clauses.push_back(clause);
                else if(lit_id != -1)
                    helper_map[lit_id].push_back(new_clause);

                sat_constraint_clauses.push_back(clause);    
            }
        }
    } else {
        encode_int_abs(*r, *r_abs, cnf_clauses);
        encode_int_abs(b, *b_abs, cnf_clauses);
        encode_int_lt(*r_abs, *b_abs, cnf_clauses);
        encode_int_plus(*bc, *r, a, cnf_clauses);        
    }

    if(export_proof){
        
        is2step = true;
        isNIA = true;
        needModDiv = true;

        constraint2step_set.insert(next_constraint_num);

        constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
        constraints2step1 << "(and\n";
        constraints2step1 << "(mzn_div " << *a.name << " " << *b.name << " " << *c.name << ")\n";
        constraints2step1 << "(ite (< " << *a.name << " 0) (<= " << *r->name << " 0) (>= " << *r->name << " 0))\n";

        constraints2step1 << "(not (= " << *b.name << " 0))\n)\n)\n";


        connection2step << "(= " << *bc->name << " (* " << *b.name << " " << *c.name << "))\n";
        connection2step << "(= " << *r_abs->name << " (ite (<= 0 " << *r->name << ") " 
                                     << *r->name << " (- " << *r->name << ")))\n";
        connection2step << "(= " << *b_abs->name << " (ite (<= 0 " << *b.name << ") " 
                                     << *b.name << " (- " << *b.name << ")))\n";
        connection2step << "(mzn_mod " << *a.name << " " << *b.name << " " << *r->name << ")\n"; 
        connection2step << "---" << endl;

        smt_step1_funs << "(define-fun f_" << *bc->name << " () Int\n";
        smt_step1_funs << "(* " << *b.name << " " << *c.name << ")\n)\n";
        smt_step1_funs << "(define-fun f_" << *r_abs->name << " () Int\n";
        smt_step1_funs << "(ite (<= 0 " << *r->name << ") " << *r->name << " (- " << *r->name << ")))\n";
        smt_step1_funs << "(define-fun f_" << *b_abs->name << " () Int\n";
        smt_step1_funs << "(ite (<= 0 " << *b.name << ") " << *b.name << " (- " << *b.name << ")))\n";
        smt_step1_funs << "(define-fun f_" << *r->name << " () Int\n";
        smt_step1_funs << "(mzn_mod_f " << *a.name << " " << *b.name << ")\n)\n";

        smt_subspace_step1 << "!(distinct " << *b.name << " 0)\n---\n";

        left_total_step1 << "(= " << *bc->name << " f_" << *bc->name << ")\n"; 
        left_total_step1 << "(= " << *r_abs->name << " f_" << *r_abs->name << ")\n"; 
        left_total_step1 << "(= " << *b_abs->name << " f_" << *b_abs->name << ")\n"; 
        left_total_step1 << "(= " << *r->name << " f_" << *r->name << ")\n"; 

        constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        constraints2step2 << "(and\n";
        constraints2step2 << "(= " << *bc->name << " (* " <<
                                     *b.name << " " << *c.name << "))\n";
        constraints2step2 << "(= " << *r_abs->name << " (ite (>= " <<
                                     *r->name << " 0) " << *r->name << " (- " << *r->name <<
                                    ")))\n";
        constraints2step2 << "(= " << *b_abs->name << " (ite (>= " <<
                                     *b.name << " 0) " << *b.name << " (- " << *b.name <<
                                    ")))\n";
        constraints2step2 << "(< " << *r_abs->name << " " << *b_abs->name << ")\n";

        constraints2step2 << "(ite (< " << *a.name << " 0) (<= " << *r->name << " 0) (>= " << *r->name << " 0))\n";

        constraints2step2 << "(= " << *a.name << " (+ " <<
                                     *bc->name << " " << *r->name << "))\n)\n)\n";
    }

    LiteralPtr pos_r = make_literal(LiteralType::ORDER, r->id, false, -1);
    LiteralPtr neg_r = make_literal(LiteralType::ORDER, r->id, true, 0);

    if(a_right < 0){
        if(r_left > 0){
            declare_unsat(cnf_clauses);
            return;
        } else if(r_right >= 0){
            cnf_clauses.push_back({neg_r});

            if(export_proof)
                sat_constraint_clauses.push_back({neg_r});
        }
    } else if(a_left > 0){
        if(r_right < 0){
            declare_unsat(cnf_clauses);
            return;
        } else if(r_left <= 0){
            cnf_clauses.push_back({pos_r});

            if(export_proof)
                sat_constraint_clauses.push_back({pos_r});
        }
    } else {

        if(r_right > 0)
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, true, -1),
                                pos_r});
        else
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, true, -1)});    

        if(r_left < 0)
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, false, 0),
                                   neg_r}); 
        else
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, false, 0)});

        if(export_proof){

            if(r_left < 0)
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, a.id, true, -1),
                                    pos_r});
            else
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, a.id, true, -1)});  

            if(r_right > 0)
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, a.id, false, 0),
                                    neg_r});
            else
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, a.id, false, 0)});
        }
    }
                     

}

// Encodes a constraint of type a = b
void Encoder::encode_int_eq(const BasicVar& a, const BasicVar& b, CNF& cnf_clauses){

    if(export_proof){
        
        isLIA = true;
        
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *a.name << " " << *b.name << ")\n)\n";

    }
 
    if(!encode_primitive_comparison_minus(a, b, 0, cnf_clauses)){
        declare_unsat(cnf_clauses);
        return;
    }
    if(!encode_primitive_comparison_minus(b, a, 0, cnf_clauses)){
        declare_unsat(cnf_clauses);
        return;
    }

}

// Encodes a constraint of type (a = b) <-> r
void Encoder::encode_int_eq_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, CNF& cnf_clauses){
 
    if(export_proof){
        
        isLIA = true;
     
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (= " <<
                                     *a.name << " " << *b.name << ") 1 0))\n)\n";
    }


    CNF temp_clauses;
    bool ret_val1, ret_val2;
    if(export_proof){
        export_proof = false;
        ret_val1 = encode_primitive_comparison_minus(a, b, 0, temp_clauses);
        ret_val2 = encode_primitive_comparison_minus(b, a, 0, temp_clauses);
        export_proof = true;
    } else { 
        ret_val1 = encode_primitive_comparison_minus(a, b, 0, temp_clauses);
        ret_val2 = encode_primitive_comparison_minus(b, a, 0, temp_clauses);
    }
    if(!ret_val1 || !ret_val2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        if(export_proof)
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
    } else
        reify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type r -> (a = b)
void Encoder::encode_int_eq_imp(const BasicVar& a, const BasicVar& b, const BasicVar& r, CNF& cnf_clauses){
 
    if(export_proof){

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (= " << *a.name << " " 
                                     << *b.name << "))\n)\n";
    }

    CNF temp_clauses;
    bool ret_val1, ret_val2;

    if(export_proof){
        export_proof = false;
        ret_val1 = encode_primitive_comparison_minus(a, b, 0, temp_clauses);
        ret_val2 = encode_primitive_comparison_minus(b, a, 0, temp_clauses);
        export_proof = true;
    } else {
        ret_val1 = encode_primitive_comparison_minus(a, b, 0, temp_clauses);
        ret_val2 = encode_primitive_comparison_minus(b, a, 0, temp_clauses);
    }

    if(!ret_val1 || !ret_val2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof)
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return;
    }
    impify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type a <= b
void Encoder::encode_int_le(const BasicVar& a, const BasicVar& b, CNF& cnf_clauses){


    if(export_proof){
        
        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";        
        trivial_encoding_constraints << "(<= " << *a.name << " " << *b.name << ")\n)\n";
    }    
    
    if(!encode_primitive_comparison_minus(a, b, 0, cnf_clauses))
        declare_unsat(cnf_clauses);

}

//Encodes a constraint of type (a <= b) <-> r
void Encoder::encode_int_le_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, CNF& cnf_clauses){

    if(export_proof){
        
        isLIA = true;
     
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (<= " <<
                                     *a.name << " " << *b.name << ") 1 0))\n)\n";
    }


    CNF temp_clauses;
    bool ret_val;
    if(export_proof){
        export_proof = false;
        ret_val = encode_primitive_comparison_minus(a, b, 0, temp_clauses);
        export_proof = true;
    } else
        ret_val = encode_primitive_comparison_minus(a, b, 0, temp_clauses);
    if(temp_clauses.empty()){
        if(!ret_val){
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});           
        }
    } else
        reify(temp_clauses, r, cnf_clauses);

}

//Encodes a constraint of type r -> (a <= b)
void Encoder::encode_int_le_imp(const BasicVar& a, const BasicVar& b, const BasicVar& r, CNF& cnf_clauses){

    if(export_proof){

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (<= " << *a.name << " " 
                                     << *b.name << "))\n)\n";
    }

    CNF temp_clauses;
    bool ret_val;

    if(export_proof){
        export_proof = false;
        ret_val = encode_primitive_comparison_minus(a, b, 0, temp_clauses);
        export_proof = true;
    } else {
        ret_val = encode_primitive_comparison_minus(a, b, 0, temp_clauses);
    }

    if(!ret_val){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof)
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return;
    }
    impify(temp_clauses, r, cnf_clauses);


}

// Encodes a substitution x = a1*x2 + a2*x2
void Encoder::encode_substitution(const BasicVar &x, const BasicVar &x1, int coef1, const BasicVar &x2, int coef2, CNF& cnf_clauses){

    if(export_proof){

        string coef1_string = coef1 < 0 ? ("(- " + to_string(-coef1) + ")") : to_string(coef1);
        string coef2_string = coef2 < 0 ? ("(- " + to_string(-coef2) + ")") : to_string(coef2);
        
        connection2step << "(= " << *x.name << " (+ (* " << coef1_string << " " << *x1.name << ") (* "
                        << coef2_string << " " << *x2.name << ")))\n";
        connection2step << "---" << endl;
                    
        constraints2step2 << "(= " << *x.name << " (+ (* " << coef1_string << " " << *x1.name << ") (* "
                          << coef2_string << " " << *x2.name << ")))\n";

        smt_step1_funs << "(define-fun f_" << *x.name<< " () Int\n";
        smt_step1_funs << "(+ (* " << coef1_string << " " << *x1.name << ") (* "
                          << coef2_string << " " << *x2.name << "))\n)\n";    
                          
        left_total_step1 << "(= " << *x.name << " f_" << *x.name << ")\n"; 
    }

    int x_left = get_left(&x);
    int x_right = get_right(&x);
    int x1_left = get_left(&x1);
    int x1_right = get_right(&x1);
    int x2_left = get_left(&x2);
    int x2_right = get_right(&x2);

    Clause new_clause;

    //-x + x1 + x2 <= 0
    int lower_bound_x1 = min({coef1*x1_left, coef1*x1_right});
    int upper_bound_x1 = max({coef1*x1_left, coef1*x1_right});
    int lower_bound_x2 = min({coef2*x2_left, coef2*x2_right});
    int upper_bound_x2 = max({coef2*x2_right, coef2*x2_left});

    for(int i = -x_right - 1; i <= -x_left; i++){
        for(int j = lower_bound_x1 - 1; j <= upper_bound_x1; j++){
            for(int k = lower_bound_x2 - 1; k <= upper_bound_x2; k++){
                if(i + j + k == -2){
                    
                    new_clause.push_back(make_literal(LiteralType::ORDER, x.id, false, -i - 1));

                    if(coef1 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, true, (int)floor((double)j/coef1)));
                    else 
                        new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, false, (int)ceil((double)j/coef1) - 1));
                    

                    if(coef2 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, true, (int)floor((double)k/coef2)));
                    else
                        new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, false, (int)ceil((double)k/coef2) - 1));

                    cnf_clauses.push_back(new_clause);

                    if(export_proof)
                        sat_constraint_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }    

    coef1 = -coef1;
    coef2 = -coef2;

    //x - x1 - x2 <= 0
    lower_bound_x1 = min({coef1*x1_left, coef1*x1_right});
    upper_bound_x1 = max({coef1*x1_left, coef1*x1_right});
    lower_bound_x2 = min({coef2*x2_left, coef2*x2_right});
    upper_bound_x2 = max({coef2*x2_right, coef2*x2_left});

    for(int i = x_left - 1; i <= x_right; i++){
        for(int j = lower_bound_x1 - 1; j <= upper_bound_x1; j++){
            for(int k = lower_bound_x2 - 1; k <= upper_bound_x2; k++){
                if(i + j + k == -2){

                    new_clause.push_back(make_literal(LiteralType::ORDER, x.id, true, i));

                    if(coef1 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, true, (int)floor((double)j/coef1)));
                    else 
                        new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, false, (int)ceil((double)j/coef1) - 1));
                    

                    if(coef2 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, true, (int)floor((double)k/coef2)));
                    else
                        new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, false, (int)ceil((double)k/coef2) - 1));                         
                
                    cnf_clauses.push_back(new_clause);

                    if(export_proof)
                        sat_constraint_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }

}

// Encodes a constraint of type a1*x1 + a2*x2 <= c
void Encoder::lin_le_2args(const BasicVar& x1, int coef1, const BasicVar& x2, int coef2, int c, CNF& cnf_clauses){

    int x1_left = get_left(&x1);
    int x1_right = get_right(&x1);
    int x2_left = get_left(&x2);
    int x2_right = get_right(&x2);

    Clause new_clause;

    int lower_bound_x1 = min({coef1*x1_left, coef1*x1_right});
    int upper_bound_x1 = max({coef1*x1_left, coef1*x1_right});
    int lower_bound_x2 = min({coef2*x2_left, coef2*x2_right});
    int upper_bound_x2 = max({coef2*x2_right, coef2*x2_left});

    for(int j = lower_bound_x1 - 1; j <= upper_bound_x1; j++){
        for(int k = lower_bound_x2 - 1; k <= upper_bound_x2; k++){
            if(j + k == -1 + c){

                if(coef1 > 0)
                    new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, true, (int)floor((double)j/coef1)));
                else 
                    new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, false, (int)ceil((double)j/coef1) - 1));
                

                if(coef2 > 0)
                    new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, true, (int)floor((double)k/coef2)));
                else
                    new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, false, (int)ceil((double)k/coef2) - 1));

                cnf_clauses.push_back(new_clause);

                if(export_proof)
                    sat_constraint_clauses.push_back(new_clause);
                new_clause.clear();
            }
        }
    }
}

// Encodes a constraint of type a1*x1 + a2*x2 + a3*x3 <= c
void Encoder::lin_le_3args(const BasicVar& x1, int coef1, const BasicVar& x2, int coef2, const BasicVar& x3, int coef3, int c, CNF& cnf_clauses){

    int x1_left = get_left(&x1);
    int x1_right = get_right(&x1);
    int x2_left = get_left(&x2);
    int x2_right = get_right(&x2);
    int x3_left = get_left(&x3);
    int x3_right = get_right(&x3);

    Clause new_clause;

    int lower_bound_x1 = min({coef1*x1_left, coef1*x1_right});
    int upper_bound_x1 = max({coef1*x1_left, coef1*x1_right});
    int lower_bound_x2 = min({coef2*x2_left, coef2*x2_right});
    int upper_bound_x2 = max({coef2*x2_right, coef2*x2_left});
    int lower_bound_x3 = min({coef3*x3_left, coef3*x3_right});
    int upper_bound_x3 = max({coef3*x3_right, coef3*x3_left});

    for(int j = lower_bound_x1 - 1; j <= upper_bound_x1; j++){
        for(int k = lower_bound_x2 - 1; k <= upper_bound_x2; k++){
            for(int l = lower_bound_x3 - 1; l <= upper_bound_x3; l++){
                if(j + k + l == -2 + c){

                    if(coef1 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, true, (int)floor((double)j/coef1)));
                    else 
                        new_clause.push_back(make_literal(LiteralType::ORDER, x1.id, false, (int)ceil((double)j/coef1) - 1));
                    

                    if(coef2 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, true, (int)floor((double)k/coef2)));
                    else
                        new_clause.push_back(make_literal(LiteralType::ORDER, x2.id, false, (int)ceil((double)k/coef2) - 1));

                    if(coef3 > 0)
                        new_clause.push_back(make_literal(LiteralType::ORDER, x3.id, true, (int)floor((double)l/coef3)));
                    else
                        new_clause.push_back(make_literal(LiteralType::ORDER, x3.id, false, (int)ceil((double)l/coef3) - 1));
                
                    cnf_clauses.push_back(new_clause);

                    if(export_proof)
                        sat_constraint_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }
}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn = c
void Encoder::encode_int_lin_eq(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, CNF& cnf_clauses){

    if(export_proof){

        if(vars.size() > 3){
            is2step = true;

            constraint2step_set.insert(next_constraint_num);

            constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
            constraints2step1 << "(= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step1 << ") "<< c_string << ")\n)\n";
            
            constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        } else {
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                trivial_encoding_constraints << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            trivial_encoding_constraints << ") "<< c_string << ")\n)\n";
        }
    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }
    if(c < sum1 || c > sum2){
        if(export_proof && is2step)
            constraints2step2 << "false\n)\n";

        declare_unsat(cnf_clauses);
        return ;
    }    

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0))});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0) - 1)});
        
        if(export_proof){

            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0))});
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0) - 1)});
        }
        return;
    }

    auto var0 = *get_var_from_array(vars, 0);
    auto var1 = *get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    if(vars.size() == 2){

        lin_le_2args(var0, coef0, var1, coef1, c, cnf_clauses);
        lin_le_2args(var0, -coef0, var1, -coef1, -c, cnf_clauses);
        return;
    }

    if(vars.size() == 3){
        auto var2 = *get_var_from_array(vars, 2);
        auto coef2 = get_int_from_array(coefs, 2);

        lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c, cnf_clauses);
        lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -c, cnf_clauses);
        return;
    }

    if(export_proof)
        constraints2step2 << "(and\n";

    int lower_bound1 = min({get_left(&var0)*coef0, get_right(&var0)*coef0});
    int upper_bound1 = max({get_left(&var0)*coef0, get_right(&var0)*coef0}); 
    int lower_bound2 = min({get_left(&var1)*coef1, get_right(&var1)*coef1});
    int upper_bound2 = max({get_left(&var1)*coef1, get_right(&var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar *sub_var;

    if(encoded_substitutions.find({var0.id, coef0, var1.id, coef1}) == 
       encoded_substitutions.end()){
        sub_var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
        encoded_substitutions[{var0.id, coef0, var1.id, coef1}] = sub_var;
        encode_substitution(*sub_var, var0, coef0, var1, coef1, cnf_clauses);
    } else {
        sub_var = encoded_substitutions[{var0.id, coef0, var1.id, coef1}];
    }

    BasicVar *sub_var1;

    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(sub_var);
        upper_bound1 = get_right(sub_var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = *get_var_from_array(vars, i);
        lower_bound2 = min({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        upper_bound2 = max({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        if(encoded_substitutions.find({sub_var->id, 1, var_i.id, coef_i}) == 
       encoded_substitutions.end()){
            sub_var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
            encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}] = sub_var1;
            encode_substitution(*sub_var1, *sub_var, 1, var_i, coef_i, cnf_clauses);
        } else {
            sub_var1 = encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}];
        }

        sub_var = sub_var1;
    }

    cnf_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c)});
    cnf_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, false, c-1)});
    if(export_proof){
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c); 
        constraints2step2 << "(= " << *sub_var1->name << " " << c_string << ")\n";

        sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c)});
        sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, false, c-1)});
    }   
    

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }


}

// Encodes a constraint of type (a1*x1 + a2*x2 + ... + an*xn = c) <-> r
void Encoder::encode_int_lin_eq_reif(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, CNF& cnf_clauses){


    if(export_proof){

        if(vars.size() > 3){
            is2step = true;

            constraint2step_set.insert(next_constraint_num);

            constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
            constraints2step1 << "(= " << *r.name << " (ite (= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step1 << ") "<< c_string << ")\n 1 0)))\n";
            
            constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        } else {
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= " << *r.name << " (ite (= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                trivial_encoding_constraints << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            trivial_encoding_constraints << ") "<< c_string << ") 1 0))\n)\n";
        }
    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }

    if(c < sum1 || c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

            if(is2step)
                constraints2step2 << "(= r 0)\n)\n";
        }

        return ;
    }    

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        LiteralPtr not_l1 = make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0));
        LiteralPtr yes_l1 = make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0));
        LiteralPtr not_l2 = make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0) - 1);
        LiteralPtr yes_l2 = make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0) - 1);
        LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
        LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

        cnf_clauses.push_back({yes_l1, not_r});
        cnf_clauses.push_back({yes_l2, not_r});
        cnf_clauses.push_back({not_l1, not_l2, yes_r});
        
        if(export_proof){
            sat_constraint_clauses.push_back({yes_l1, not_r});
            sat_constraint_clauses.push_back({yes_l2, not_r});
            sat_constraint_clauses.push_back({not_l1, not_l2, yes_r});
        }
        return;
    }

    auto var0 = *get_var_from_array(vars, 0);
    auto var1 = *get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    if(vars.size() == 2){
        CNF temp_clauses;

        if(export_proof){
            export_proof = false;
            lin_le_2args(var0, coef0, var1, coef1, c, temp_clauses);
            lin_le_2args(var0, -coef0, var1, -coef1, -c, temp_clauses);
            export_proof = true;
        } else {
            lin_le_2args(var0, coef0, var1, coef1, c, temp_clauses);
            lin_le_2args(var0, -coef0, var1, -coef1, -c, temp_clauses);           
        }
        
        reify(temp_clauses, r, cnf_clauses);
        return;
    }

    if(vars.size() == 3){
        CNF temp_clauses;
        auto var2 = *get_var_from_array(vars, 2);
        auto coef2 = get_int_from_array(coefs, 2);

        if(export_proof){
            export_proof = false;
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c, temp_clauses);
            lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -c, temp_clauses);
            export_proof = true;
        } else {
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c, temp_clauses);
            lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -c, temp_clauses);            
        }

        reify(temp_clauses, r, cnf_clauses);
        return;
    }

    if(export_proof)
        constraints2step2 << "(and\n";

    int lower_bound1 = min({get_left(&var0)*coef0, get_right(&var0)*coef0});
    int upper_bound1 = max({get_left(&var0)*coef0, get_right(&var0)*coef0}); 
    int lower_bound2 = min({get_left(&var1)*coef1, get_right(&var1)*coef1});
    int upper_bound2 = max({get_left(&var1)*coef1, get_right(&var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar *sub_var;

    if(encoded_substitutions.find({var0.id, coef0, var1.id, coef1}) == 
       encoded_substitutions.end()){
        sub_var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
        encoded_substitutions[{var0.id, coef0, var1.id, coef1}] = sub_var;
        encode_substitution(*sub_var, var0, coef0, var1, coef1, cnf_clauses);
    } else {
        sub_var = encoded_substitutions[{var0.id, coef0, var1.id, coef1}];
    }

    BasicVar *sub_var1;

    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(sub_var);
        upper_bound1 = get_right(sub_var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = *get_var_from_array(vars, i);
        lower_bound2 = min({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        upper_bound2 = max({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        if(encoded_substitutions.find({sub_var->id, 1, var_i.id, coef_i}) == 
       encoded_substitutions.end()){
            sub_var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
            encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}] = sub_var1;
            encode_substitution(*sub_var1, *sub_var, 1, var_i, coef_i, cnf_clauses);
        } else {
            sub_var1 = encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}];
        }

        sub_var = sub_var1;
    }

    CNF temp_clauses;

    temp_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c)});
    temp_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, false, c-1)});
    if(export_proof){
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c); 
        constraints2step2 << "(= " << *r.name << 
                                " (ite (= " << *sub_var1->name << " " << c_string << ") 1 0))\n";

    }   
    
    reify(temp_clauses, r, cnf_clauses);

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }

}

// Encodes a constraint of type r -> (a1*x1 + a2*x2 + ... + an*xn = c)
void Encoder::encode_int_lin_eq_imp(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, CNF& cnf_clauses){


    if(export_proof){

        if(vars.size() > 3){
            is2step = true;

            constraint2step_set.insert(next_constraint_num);

            constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
            constraints2step1 << "(=> (= " << *r.name << " 1) (= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step1 << ") "<< c_string << "))\n)\n";
            
            constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        } else {
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                trivial_encoding_constraints << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            trivial_encoding_constraints << ") "<< c_string << "))\n)\n";
        }
    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }

    if(c < sum1 || c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

            if(is2step)
                constraints2step2 << "(= r 0)\n)\n";
        }

        return ;
    }    

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        LiteralPtr not_l1 = make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0));
        LiteralPtr yes_l1 = make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0));
        LiteralPtr not_l2 = make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0) - 1);
        LiteralPtr yes_l2 = make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0) - 1);
        LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
        LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

        cnf_clauses.push_back({yes_l1, not_r});
        cnf_clauses.push_back({yes_l2, not_r});
        
        if(export_proof){
            sat_constraint_clauses.push_back({yes_l1, not_r});
            sat_constraint_clauses.push_back({yes_l2, not_r});
        }
        return;
    }

    auto var0 = *get_var_from_array(vars, 0);
    auto var1 = *get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    if(vars.size() == 2){
        CNF temp_clauses;

        if(export_proof){
            export_proof = false;
            lin_le_2args(var0, coef0, var1, coef1, c, temp_clauses);
            lin_le_2args(var0, -coef0, var1, -coef1, -c, temp_clauses);
            export_proof = true;
        } else {
            lin_le_2args(var0, coef0, var1, coef1, c, temp_clauses);
            lin_le_2args(var0, -coef0, var1, -coef1, -c, temp_clauses);           
        }
        
        impify(temp_clauses, r, cnf_clauses);
        return;
    }

    if(vars.size() == 3){
        CNF temp_clauses;
        auto var2 = *get_var_from_array(vars, 2);
        auto coef2 = get_int_from_array(coefs, 2);

        if(export_proof){
            export_proof = false;
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c, temp_clauses);
            lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -c, temp_clauses);
            export_proof = true;
        } else {
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c, temp_clauses);
            lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -c, temp_clauses);            
        }

        impify(temp_clauses, r, cnf_clauses);
        return;
    }

    if(export_proof)
        constraints2step2 << "(and\n";

    int lower_bound1 = min({get_left(&var0)*coef0, get_right(&var0)*coef0});
    int upper_bound1 = max({get_left(&var0)*coef0, get_right(&var0)*coef0}); 
    int lower_bound2 = min({get_left(&var1)*coef1, get_right(&var1)*coef1});
    int upper_bound2 = max({get_left(&var1)*coef1, get_right(&var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar *sub_var;

    if(encoded_substitutions.find({var0.id, coef0, var1.id, coef1}) == 
       encoded_substitutions.end()){
        sub_var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
        encoded_substitutions[{var0.id, coef0, var1.id, coef1}] = sub_var;
        encode_substitution(*sub_var, var0, coef0, var1, coef1, cnf_clauses);
    } else {
        sub_var = encoded_substitutions[{var0.id, coef0, var1.id, coef1}];
    }

    BasicVar *sub_var1;

    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(sub_var);
        upper_bound1 = get_right(sub_var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = *get_var_from_array(vars, i);
        lower_bound2 = min({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        upper_bound2 = max({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        if(encoded_substitutions.find({sub_var->id, 1, var_i.id, coef_i}) == 
       encoded_substitutions.end()){
            sub_var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
            encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}] = sub_var1;
            encode_substitution(*sub_var1, *sub_var, 1, var_i, coef_i, cnf_clauses);
        } else {
            sub_var1 = encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}];
        }

        sub_var = sub_var1;
    }

    CNF temp_clauses;

    temp_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c)});
    temp_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, false, c-1)});
    if(export_proof){
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c); 
        constraints2step2 << "(=> (= " << *r.name << " 1) " 
                                " (= " << *sub_var1->name << " " << c_string << ")\n)\n";

    }   
    
    impify(temp_clauses, r, cnf_clauses);

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }

}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn <= c
void Encoder::encode_int_lin_le(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, CNF& cnf_clauses){


    if(export_proof){

        if(vars.size() > 3){
            is2step = true;

            constraint2step_set.insert(next_constraint_num);

            constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
            constraints2step1 << "(<= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step1 << ") "<< c_string << ")\n)\n";
            
            constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        } else {
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(<= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                trivial_encoding_constraints << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            trivial_encoding_constraints << ") "<< c_string << ")\n)\n";
        }
    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }

    if(c < sum1){
        if(export_proof && is2step)
            constraints2step2 << "false\n)\n";

        declare_unsat(cnf_clauses);
        return ;
    }    

    if(c > sum2){
        if(export_proof && is2step){
            constraints2step2 << "true\n)\n";
            auto var = get_var_from_array(vars, 0);

            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, get_right(var))});
        }
        return ;
    }    


    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0))});
        if(export_proof){     
            
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0))});
        }
        return;
    }

    auto var0 = *get_var_from_array(vars, 0);
    auto var1 = *get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    if(vars.size() == 2){
        lin_le_2args(var0, coef0, var1, coef1, c, cnf_clauses);
        return;
    }

    if(vars.size() == 3){
        auto var2 = *get_var_from_array(vars, 2);
        auto coef2 = get_int_from_array(coefs, 2);

        lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c, cnf_clauses);
        return;
    }

    if(export_proof)
        constraints2step2 << "(and\n";

    int lower_bound1 = min({get_left(&var0)*coef0, get_right(&var0)*coef0});
    int upper_bound1 = max({get_left(&var0)*coef0, get_right(&var0)*coef0}); 
    int lower_bound2 = min({get_left(&var1)*coef1, get_right(&var1)*coef1});
    int upper_bound2 = max({get_left(&var1)*coef1, get_right(&var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar *sub_var;

    if(encoded_substitutions.find({var0.id, coef0, var1.id, coef1}) == 
       encoded_substitutions.end()){
        sub_var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
        encoded_substitutions[{var0.id, coef0, var1.id, coef1}] = sub_var;
        encode_substitution(*sub_var, var0, coef0, var1, coef1, cnf_clauses);
    } else {
        sub_var = encoded_substitutions[{var0.id, coef0, var1.id, coef1}];
    }

    BasicVar *sub_var1;

    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(sub_var);
        upper_bound1 = get_right(sub_var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = *get_var_from_array(vars, i);
        lower_bound2 = min({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        upper_bound2 = max({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        if(encoded_substitutions.find({sub_var->id, 1, var_i.id, coef_i}) == 
       encoded_substitutions.end()){
            sub_var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
            encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}] = sub_var1;
            encode_substitution(*sub_var1, *sub_var, 1, var_i, coef_i, cnf_clauses);
        } else {
            sub_var1 = encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}];
        }

        sub_var = sub_var1;
    }

    cnf_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c)});
    if(export_proof){
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);  
        constraints2step2 << "(<= sub_" << sub_var1->id << " " <<  c_string << ")\n";

        sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c)});
    }
    

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }
}

// Encodes a constraint of type (a1*x1 + a2*x2 + ... + an*xn <= c) <-> r
void Encoder::encode_int_lin_le_reif(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, CNF& cnf_clauses){



    if(export_proof){

        if(vars.size() > 3){
            is2step = true;

            constraint2step_set.insert(next_constraint_num);

            constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
            constraints2step1 << "(= " << *r.name << " (ite (<= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step1 << ") "<< c_string << ")\n 1 0)))\n";
            
            constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        } else {
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= " << *r.name << " (ite (<= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                trivial_encoding_constraints << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            trivial_encoding_constraints << ") "<< c_string << ") 1 0))\n)\n";
        }
    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }

    if(c < sum1){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

            constraints2step2 << "(= r 0)\n)\n";
        }

        return ;
    }    

    if(c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});

        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});

            if(is2step)
                constraints2step2 << "(= r 1)\n)\n";
        }

        return ;
    }   

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        LiteralPtr not_l1 = make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0));
        LiteralPtr yes_l1 = make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0));
        LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
        LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

        cnf_clauses.push_back({yes_l1, not_r});
        cnf_clauses.push_back({not_l1, yes_r});
        
        if(export_proof){
            sat_constraint_clauses.push_back({yes_l1, not_r});
            sat_constraint_clauses.push_back({not_l1, yes_r});
        }
        return;
    }

    auto var0 = *get_var_from_array(vars, 0);
    auto var1 = *get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    if(vars.size() == 2){
        CNF temp_clauses;

        if(export_proof){
            export_proof = false;
            lin_le_2args(var0, coef0, var1, coef1, c, temp_clauses);
            export_proof = true;
        } else {
            lin_le_2args(var0, coef0, var1, coef1, c, temp_clauses);         
        }
        
        reify(temp_clauses, r, cnf_clauses);
        return;
    }

    if(vars.size() == 3){
        CNF temp_clauses;
        auto var2 = *get_var_from_array(vars, 2);
        auto coef2 = get_int_from_array(coefs, 2);

        if(export_proof){
            export_proof = false;
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c, temp_clauses);
            export_proof = true;
        } else {
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c, temp_clauses);          
        }

        reify(temp_clauses, r, cnf_clauses);
        return;
    }

    if(export_proof)
        constraints2step2 << "(and\n";

    int lower_bound1 = min({get_left(&var0)*coef0, get_right(&var0)*coef0});
    int upper_bound1 = max({get_left(&var0)*coef0, get_right(&var0)*coef0}); 
    int lower_bound2 = min({get_left(&var1)*coef1, get_right(&var1)*coef1});
    int upper_bound2 = max({get_left(&var1)*coef1, get_right(&var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar *sub_var;

    if(encoded_substitutions.find({var0.id, coef0, var1.id, coef1}) == 
       encoded_substitutions.end()){
        sub_var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
        encoded_substitutions[{var0.id, coef0, var1.id, coef1}] = sub_var;
        encode_substitution(*sub_var, var0, coef0, var1, coef1, cnf_clauses);
    } else {
        sub_var = encoded_substitutions[{var0.id, coef0, var1.id, coef1}];
    }

    BasicVar *sub_var1;

    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(sub_var);
        upper_bound1 = get_right(sub_var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = *get_var_from_array(vars, i);
        lower_bound2 = min({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        upper_bound2 = max({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        if(encoded_substitutions.find({sub_var->id, 1, var_i.id, coef_i}) == 
       encoded_substitutions.end()){
            sub_var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
            encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}] = sub_var1;
            encode_substitution(*sub_var1, *sub_var, 1, var_i, coef_i, cnf_clauses);
        } else {
            sub_var1 = encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}];
        }

        sub_var = sub_var1;
    }

    CNF temp_clauses;

    temp_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c)});
    if(export_proof){
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c); 
        constraints2step2 << "(= " << *r.name << 
                                " (ite (<= " << *sub_var1->name << " " << c_string << ") 1 0))\n";

    }   
    
    reify(temp_clauses, r, cnf_clauses);

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }

}

// Encodes a constraint of type r -> (a1*x1 + a2*x2 + ... + an*xn <= c)
void Encoder::encode_int_lin_le_imp(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, CNF& cnf_clauses){



    if(export_proof){

        if(vars.size() > 3){
            is2step = true;

            constraint2step_set.insert(next_constraint_num);

            constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
            constraints2step1 << "(=> (= " << *r.name << " 1) (<= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step1 << ") "<< c_string << ")\n ))\n";
            
            constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        } else {
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (<= (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                trivial_encoding_constraints << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            trivial_encoding_constraints << ") "<< c_string << "))\n)\n";
        }
    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }

    if(c < sum1){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

            constraints2step2 << "(= r 0)\n)\n";
        }

        return ;
    }    

    if(c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0),
                                   make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

            if(is2step)
                constraints2step2 << "true\n)\n";
        }

        return ;
    }   

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        LiteralPtr not_l1 = make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0));
        LiteralPtr yes_l1 = make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0));
        LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
        LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

        cnf_clauses.push_back({yes_l1, not_r});
        
        if(export_proof){
            sat_constraint_clauses.push_back({yes_l1, not_r});
        }
        return;
    }

    auto var0 = *get_var_from_array(vars, 0);
    auto var1 = *get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    if(vars.size() == 2){
        CNF temp_clauses;

        if(export_proof){
            export_proof = false;
            lin_le_2args(var0, coef0, var1, coef1, c, temp_clauses);
            export_proof = true;
        } else {
            lin_le_2args(var0, coef0, var1, coef1, c, temp_clauses);         
        }
        
        impify(temp_clauses, r, cnf_clauses);
        return;
    }

    if(vars.size() == 3){
        CNF temp_clauses;
        auto var2 = *get_var_from_array(vars, 2);
        auto coef2 = get_int_from_array(coefs, 2);

        if(export_proof){
            export_proof = false;
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c, temp_clauses);
            export_proof = true;
        } else {
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c, temp_clauses);          
        }

        impify(temp_clauses, r, cnf_clauses);
        return;
    }

    if(export_proof)
        constraints2step2 << "(and\n";

    int lower_bound1 = min({get_left(&var0)*coef0, get_right(&var0)*coef0});
    int upper_bound1 = max({get_left(&var0)*coef0, get_right(&var0)*coef0}); 
    int lower_bound2 = min({get_left(&var1)*coef1, get_right(&var1)*coef1});
    int upper_bound2 = max({get_left(&var1)*coef1, get_right(&var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar *sub_var;

    if(encoded_substitutions.find({var0.id, coef0, var1.id, coef1}) == 
       encoded_substitutions.end()){
        sub_var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
        encoded_substitutions[{var0.id, coef0, var1.id, coef1}] = sub_var;
        encode_substitution(*sub_var, var0, coef0, var1, coef1, cnf_clauses);
    } else {
        sub_var = encoded_substitutions[{var0.id, coef0, var1.id, coef1}];
    }

    BasicVar *sub_var1;

    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(sub_var);
        upper_bound1 = get_right(sub_var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = *get_var_from_array(vars, i);
        lower_bound2 = min({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        upper_bound2 = max({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        if(encoded_substitutions.find({sub_var->id, 1, var_i.id, coef_i}) == 
       encoded_substitutions.end()){
            sub_var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
            encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}] = sub_var1;
            encode_substitution(*sub_var1, *sub_var, 1, var_i, coef_i, cnf_clauses);
        } else {
            sub_var1 = encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}];
        }

        sub_var = sub_var1;
    }

    CNF temp_clauses;

    temp_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c)});
    if(export_proof){
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c); 
        constraints2step2 << "(=> (= " << *r.name << " 1) " 
                                " (<= " << *sub_var1->name << " " << c_string << ")\n)\n";

    }   
    
    impify(temp_clauses, r, cnf_clauses);

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }

}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn =/= c
void Encoder::encode_int_lin_ne(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, CNF& cnf_clauses){   

    if(export_proof){

        if(vars.size() > 3){
            is2step = true;

            constraint2step_set.insert(next_constraint_num);

            constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
            constraints2step1 << "(distinct (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step1 << ") "<< c_string << ")\n)\n";
            
            constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        } else {
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(distinct (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                trivial_encoding_constraints << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            trivial_encoding_constraints << ") "<< c_string << ")\n)\n";
        }
    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }
    if(c < sum1 || c > sum2){
        if(export_proof && is2step){
            constraints2step2 << "true\n)\n";
            auto var = get_var_from_array(vars, 0);

            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, get_right(var))});
        }

        return ;
    } 


    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0) - 1),
                               make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0))});
        if(export_proof){
                                         
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0) - 1),
                               make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0))});
        }
        return;
    }

    auto var0 = *get_var_from_array(vars, 0);
    auto var1 = *get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);


    if(vars.size() == 2){
        CNF temp_clauses;

        if(export_proof){
            export_proof = false;
            lin_le_2args(var0, coef0, var1, coef1, c - 1, temp_clauses);
            export_proof = true;
        } else {
            lin_le_2args(var0, coef0, var1, coef1, c - 1, temp_clauses);
        }

        LiteralPtr not_helper1 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        for(auto c : temp_clauses){
            if(export_proof)
                helper_map[not_helper1->id].push_back(c);

            c.push_back(not_helper1);
            cnf_clauses.push_back(c);

            if(export_proof)
                sat_constraint_clauses.push_back(c);
        }

        temp_clauses.clear();

        if(export_proof){
            export_proof = false;
            lin_le_2args(var0, -coef0, var1, -coef1, -(c + 1), temp_clauses);
            export_proof = true;
        } else {
            lin_le_2args(var0, -coef0, var1, -coef1, -(c + 1), temp_clauses);
        }
        LiteralPtr not_helper2 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        for(auto c : temp_clauses){
            if(export_proof)
                helper_map[not_helper2->id].push_back(c);

            c.push_back(not_helper2);
            cnf_clauses.push_back(c);

            if(export_proof)
                sat_constraint_clauses.push_back(c);
        }

        cnf_clauses.push_back({yes_helper1, yes_helper2});
        if(export_proof){
            definition_clauses.push_back({yes_helper1, yes_helper2});
            sat_constraint_clauses.push_back({yes_helper1, yes_helper2});
        }

        return;
    }

    if(vars.size() == 3){
        CNF temp_clauses;
        auto var2 = *get_var_from_array(vars, 2);
        auto coef2 = get_int_from_array(coefs, 2);        

        if(export_proof){
            export_proof = false;
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c - 1, temp_clauses);
            export_proof = true;
        } else {
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c - 1, temp_clauses);
        }

        LiteralPtr not_helper1 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        for(auto c : temp_clauses){
            if(export_proof)
                helper_map[not_helper1->id].push_back(c);

            c.push_back(not_helper1);
            cnf_clauses.push_back(c);

            if(export_proof)
                sat_constraint_clauses.push_back(c);
        }

        temp_clauses.clear();

        if(export_proof){
            export_proof = false;
            lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -(c + 1), temp_clauses);
            export_proof = true;
        } else {
            lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -(c + 1), temp_clauses);
        }
        LiteralPtr not_helper2 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        for(auto c : temp_clauses){
            if(export_proof)
                helper_map[not_helper2->id].push_back(c);

            c.push_back(not_helper2);
            cnf_clauses.push_back(c);

            if(export_proof)
                sat_constraint_clauses.push_back(c);
        }

        cnf_clauses.push_back({yes_helper1, yes_helper2});
        if(export_proof){
            definition_clauses.push_back({yes_helper1, yes_helper2});
            sat_constraint_clauses.push_back({yes_helper1, yes_helper2});
        }

        return;
    }

    if(export_proof)
        constraints2step2 << "(and\n";

    int lower_bound1 = min({get_left(&var0)*coef0, get_right(&var0)*coef0});
    int upper_bound1 = max({get_left(&var0)*coef0, get_right(&var0)*coef0}); 
    int lower_bound2 = min({get_left(&var1)*coef1, get_right(&var1)*coef1});
    int upper_bound2 = max({get_left(&var1)*coef1, get_right(&var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar *sub_var;

    if(encoded_substitutions.find({var0.id, coef0, var1.id, coef1}) == 
       encoded_substitutions.end()){
        sub_var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
        encoded_substitutions[{var0.id, coef0, var1.id, coef1}] = sub_var;
        encode_substitution(*sub_var, var0, coef0, var1, coef1, cnf_clauses);
    } else {
        sub_var = encoded_substitutions[{var0.id, coef0, var1.id, coef1}];
    }

    BasicVar *sub_var1;

    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(sub_var);
        upper_bound1 = get_right(sub_var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = *get_var_from_array(vars, i);
        lower_bound2 = min({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        upper_bound2 = max({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        if(encoded_substitutions.find({sub_var->id, 1, var_i.id, coef_i}) == 
       encoded_substitutions.end()){
            sub_var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
            encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}] = sub_var1;
            encode_substitution(*sub_var1, *sub_var, 1, var_i, coef_i, cnf_clauses);
        } else {
            sub_var1 = encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}];
        }

        sub_var = sub_var1;
    }


    cnf_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c - 1),
                            make_literal(LiteralType::ORDER, sub_var1->id, false, c)});
    if(export_proof){
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c); 
        constraints2step2 << "(distinct " << *sub_var1->name << " " << c_string << ")\n";

        sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c - 1),
                            make_literal(LiteralType::ORDER, sub_var1->id, false, c)});
    }   
    

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }

}

// Encodes a constraint of type (a1*x1 + a2*x2 + ... + an*xn =/= c) <-> r
void Encoder::encode_int_lin_ne_reif(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, CNF& cnf_clauses){

    if(export_proof){

        if(vars.size() > 3){
            is2step = true;

            constraint2step_set.insert(next_constraint_num);

            constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
            constraints2step1 << "(= " << *r.name << " (ite (distinct (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step1 << ") "<< c_string << ")\n 1 0)))\n";
            
            constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        } else {
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= " << *r.name << " (ite (distinct (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                trivial_encoding_constraints << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            trivial_encoding_constraints << ") "<< c_string << ") 1 0))\n)\n";
        }
    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }

    if(c < sum1 || c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        
        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});

            if(is2step)
                constraints2step2 << "(= r 1)\n)\n";
        }

        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0) - 1),
                               make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0) - 1),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0) - 1),
                                make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                                make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0) - 1),
                                make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0)),
                                make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
        }   
        return;
    }

    auto var0 = *get_var_from_array(vars, 0);
    auto var1 = *get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    if(vars.size() == 2){
        CNF temp_clauses;

        if(export_proof){
            export_proof = false;
            lin_le_2args(var0, coef0, var1, coef1, c - 1, temp_clauses);
            export_proof = true;
        } else {
            lin_le_2args(var0, coef0, var1, coef1, c - 1, temp_clauses);
        }

        LiteralPtr not_helper1 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        reify_helper(temp_clauses, not_helper1, cnf_clauses);

        temp_clauses.clear();

        if(export_proof){
            export_proof = false;
            lin_le_2args(var0, -coef0, var1, -coef1, -(c + 1), temp_clauses);
            export_proof = true;
        } else {
            lin_le_2args(var0, -coef0, var1, -coef1, -(c + 1), temp_clauses);
        }
        LiteralPtr not_helper2 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        reify_helper(temp_clauses, not_helper2, cnf_clauses);

        LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
        LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

        cnf_clauses.push_back({yes_helper1, yes_helper2, not_r});
        cnf_clauses.push_back({not_helper1, yes_r});
        cnf_clauses.push_back({not_helper2, yes_r});
        
        if(export_proof){
            sat_constraint_clauses.push_back({yes_helper1, yes_helper2, not_r});
            sat_constraint_clauses.push_back({not_helper1, yes_r});
            sat_constraint_clauses.push_back({not_helper2, yes_r});
        
            definition_clauses.push_back({yes_helper1, yes_helper2, not_r});
            definition_clauses.push_back({not_helper1, yes_r});
            definition_clauses.push_back({not_helper2, yes_r});
        }

        return;
    }


    if(vars.size() == 3){
        CNF temp_clauses;
        auto var2 = *get_var_from_array(vars, 2);
        auto coef2 = get_int_from_array(coefs, 2);

        if(export_proof){
            export_proof = false;
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c - 1, temp_clauses);
            export_proof = true;
        } else {
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c - 1, temp_clauses);
        }

        LiteralPtr not_helper1 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        reify_helper(temp_clauses, not_helper1, cnf_clauses);

        temp_clauses.clear();

        if(export_proof){
            export_proof = false;
            lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -(c + 1), temp_clauses);
            export_proof = true;
        } else {
            lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -(c + 1), temp_clauses);
        }
        LiteralPtr not_helper2 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        reify_helper(temp_clauses, not_helper2, cnf_clauses);

        LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
        LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

        cnf_clauses.push_back({yes_helper1, yes_helper2, not_r});
        cnf_clauses.push_back({not_helper1, yes_r});
        cnf_clauses.push_back({not_helper2, yes_r});
        
        if(export_proof){
            sat_constraint_clauses.push_back({yes_helper1, yes_helper2, not_r});
            sat_constraint_clauses.push_back({not_helper1, yes_r});
            sat_constraint_clauses.push_back({not_helper2, yes_r});
        
            definition_clauses.push_back({yes_helper1, yes_helper2, not_r});
            definition_clauses.push_back({not_helper1, yes_r});
            definition_clauses.push_back({not_helper2, yes_r});
        }

        return;
    }


    if(export_proof)
        constraints2step2 << "(and\n";

    int lower_bound1 = min({get_left(&var0)*coef0, get_right(&var0)*coef0});
    int upper_bound1 = max({get_left(&var0)*coef0, get_right(&var0)*coef0}); 
    int lower_bound2 = min({get_left(&var1)*coef1, get_right(&var1)*coef1});
    int upper_bound2 = max({get_left(&var1)*coef1, get_right(&var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar *sub_var;

    if(encoded_substitutions.find({var0.id, coef0, var1.id, coef1}) == 
       encoded_substitutions.end()){
        sub_var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
        encoded_substitutions[{var0.id, coef0, var1.id, coef1}] = sub_var;
        encode_substitution(*sub_var, var0, coef0, var1, coef1, cnf_clauses);
    } else {
        sub_var = encoded_substitutions[{var0.id, coef0, var1.id, coef1}];
    }

    BasicVar *sub_var1;

    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(sub_var);
        upper_bound1 = get_right(sub_var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = *get_var_from_array(vars, i);
        lower_bound2 = min({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        upper_bound2 = max({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        if(encoded_substitutions.find({sub_var->id, 1, var_i.id, coef_i}) == 
       encoded_substitutions.end()){
            sub_var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
            encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}] = sub_var1;
            encode_substitution(*sub_var1, *sub_var, 1, var_i, coef_i, cnf_clauses);
        } else {
            sub_var1 = encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}];
        }

        sub_var = sub_var1;
    }

    CNF temp_clauses;

    temp_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c - 1),
                            make_literal(LiteralType::ORDER, sub_var1->id, false, c)});
    if(export_proof){
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c); 
        constraints2step2 << "(= " << *r.name << 
                                " (ite (distinct " << *sub_var1->name << " " << c_string << ") 1 0))\n";
    }   
    
    reify(temp_clauses, r, cnf_clauses);

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }
}

// Encodes a constraint of type r -> (a1*x1 + a2*x2 + ... + an*xn =/= c)
void Encoder::encode_int_lin_ne_imp(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, const BasicVar& r, CNF& cnf_clauses){

    if(export_proof){

        if(vars.size() > 3){
            is2step = true;

            constraint2step_set.insert(next_constraint_num);

            constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
            constraints2step1 << "(=> (= " << *r.name << " 1) (distinct (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step1 << ") "<< c_string << ")\n))\n";
            
            constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        } else {
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (distinct (+ ";
            for(int i = 0; i < (int)vars.size(); i++){
                int coef = get_int_from_array(coefs, i);
                string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
                auto var = get_var_from_array(vars, i);
                trivial_encoding_constraints << "(* " << coef_string << " " << *var->name << ") ";
            }
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            trivial_encoding_constraints << ") "<< c_string << "))\n)\n";
        }
    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        auto var = get_var_from_array(vars, i);
        auto left = get_left(var);
        auto right = get_right(var);
        if(coef > 0){
            sum1 += coef * left;
            sum2 += coef * right;
        } else {
            sum1 += coef * right;
            sum2 += coef * left;
        }
    }

    if(c < sum1 || c > sum2){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0), make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        
        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0), make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        }

        return ;        
    }

    if(vars.size() == 1){
        auto var = get_var_from_array(vars, 0);
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0) - 1),
                               make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                               make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c/get_int_from_array(coefs, 0) - 1),
                                make_literal(LiteralType::ORDER, var->id, false, c/get_int_from_array(coefs, 0)),
                                make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        }   
        return;
    }

    auto var0 = *get_var_from_array(vars, 0);
    auto var1 = *get_var_from_array(vars, 1);
    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    if(vars.size() == 2){
        CNF temp_clauses;

        if(export_proof){
            export_proof = false;
            lin_le_2args(var0, coef0, var1, coef1, c - 1, temp_clauses);
            export_proof = true;
        } else {
            lin_le_2args(var0, coef0, var1, coef1, c - 1, temp_clauses);
        }

        LiteralPtr not_helper1 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        reify_helper(temp_clauses, not_helper1, cnf_clauses);

        temp_clauses.clear();

        if(export_proof){
            export_proof = false;
            lin_le_2args(var0, -coef0, var1, -coef1, -(c + 1), temp_clauses);
            export_proof = true;
        } else {
            lin_le_2args(var0, -coef0, var1, -coef1, -(c + 1), temp_clauses);
        }
        LiteralPtr not_helper2 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        reify_helper(temp_clauses, not_helper2, cnf_clauses);

        LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
        LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

        cnf_clauses.push_back({yes_helper1, yes_helper2, not_r});
        
        if(export_proof){
            sat_constraint_clauses.push_back({yes_helper1, yes_helper2, not_r});
        
            definition_clauses.push_back({yes_helper1, yes_helper2, not_r});
        }

        return;
    }


    if(vars.size() == 3){
        CNF temp_clauses;
        auto var2 = *get_var_from_array(vars, 2);
        auto coef2 = get_int_from_array(coefs, 2);

        if(export_proof){
            export_proof = false;
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c - 1, temp_clauses);
            export_proof = true;
        } else {
            lin_le_3args(var0, coef0, var1, coef1, var2, coef2, c - 1, temp_clauses);
        }

        LiteralPtr not_helper1 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        reify_helper(temp_clauses, not_helper1, cnf_clauses);

        temp_clauses.clear();

        if(export_proof){
            export_proof = false;
            lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -(c + 1), temp_clauses);
            export_proof = true;
        } else {
            lin_le_3args(var0, -coef0, var1, -coef1, var2, -coef2, -(c + 1), temp_clauses);
        }
        LiteralPtr not_helper2 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

        reify_helper(temp_clauses, not_helper2, cnf_clauses);

        LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
        LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

        cnf_clauses.push_back({yes_helper1, yes_helper2, not_r});
        
        if(export_proof){
            sat_constraint_clauses.push_back({yes_helper1, yes_helper2, not_r});
        
            definition_clauses.push_back({yes_helper1, yes_helper2, not_r});
        }

        return;
    }


    if(export_proof)
        constraints2step2 << "(and\n";

    int lower_bound1 = min({get_left(&var0)*coef0, get_right(&var0)*coef0});
    int upper_bound1 = max({get_left(&var0)*coef0, get_right(&var0)*coef0}); 
    int lower_bound2 = min({get_left(&var1)*coef1, get_right(&var1)*coef1});
    int upper_bound2 = max({get_left(&var1)*coef1, get_right(&var1)*coef1}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar *sub_var;

    if(encoded_substitutions.find({var0.id, coef0, var1.id, coef1}) == 
       encoded_substitutions.end()){
        sub_var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
        encoded_substitutions[{var0.id, coef0, var1.id, coef1}] = sub_var;
        encode_substitution(*sub_var, var0, coef0, var1, coef1, cnf_clauses);
    } else {
        sub_var = encoded_substitutions[{var0.id, coef0, var1.id, coef1}];
    }

    BasicVar *sub_var1;

    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(sub_var);
        upper_bound1 = get_right(sub_var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = *get_var_from_array(vars, i);
        lower_bound2 = min({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        upper_bound2 = max({get_left(&var_i)*coef_i, get_right(&var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        if(encoded_substitutions.find({sub_var->id, 1, var_i.id, coef_i}) == 
       encoded_substitutions.end()){
            sub_var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
            encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}] = sub_var1;
            encode_substitution(*sub_var1, *sub_var, 1, var_i, coef_i, cnf_clauses);
        } else {
            sub_var1 = encoded_substitutions[{sub_var->id, 1, var_i.id, coef_i}];
        }

        sub_var = sub_var1;
    }

    CNF temp_clauses;

    temp_clauses.push_back({make_literal(LiteralType::ORDER, sub_var1->id, true, c - 1),
                            make_literal(LiteralType::ORDER, sub_var1->id, false, c)});
    if(export_proof){
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c); 
        constraints2step2 << "(=> (= " << *r.name << " 1)"
                                " (distinct " << *sub_var1->name << " " << c_string << "))\n";
    }   
    
    impify(temp_clauses, r, cnf_clauses);

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }
}

// Encodes a constraint of type a < b
void Encoder::encode_int_lt(const BasicVar& a, const BasicVar& b, CNF& cnf_clauses){

    if(export_proof){
        
        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";        
        trivial_encoding_constraints << "(< " << *a.name << " " << *b.name << ")\n)\n";
    }    

    if(!encode_primitive_comparison_minus(a, b, -1, cnf_clauses))
        declare_unsat(cnf_clauses);

}

// Encodes a constraint of type (a < b) <-> r
void Encoder::encode_int_lt_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, CNF& cnf_clauses){

    if(export_proof){
        
        isLIA = true;
     
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (< " <<
                                     *a.name << " " << *b.name << ") 1 0))\n)\n";
    }


    CNF temp_clauses;
    bool ret_val;
    if(export_proof){
        export_proof = false;
        ret_val = encode_primitive_comparison_minus(a, b, -1, temp_clauses);
        export_proof = true;
    } else
        ret_val = encode_primitive_comparison_minus(a, b, -1, temp_clauses);
    if(temp_clauses.empty()){
        if(!ret_val){
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        } else {
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});
            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0)});           
        }
    } else
        reify(temp_clauses, r, cnf_clauses);
    

}

// Encodes a constraint of type r -> (a < b)
void Encoder::encode_int_lt_imp(const BasicVar& a, const BasicVar& b, const BasicVar& r, CNF& cnf_clauses){

    if(export_proof){

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (< " << *a.name << " " 
                                     << *b.name << "))\n)\n";
    }

    CNF temp_clauses;
    bool ret_val;

    if(export_proof){
        export_proof = false;
        ret_val = encode_primitive_comparison_minus(a, b, -1, temp_clauses);
        export_proof = true;
    } else {
        ret_val = encode_primitive_comparison_minus(a, b, -1, temp_clauses);
    }

    if(!ret_val){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof)
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});
        return;
    }
    impify(temp_clauses, r, cnf_clauses);


}

// Encodes a constraint of type max(a, b) = c
void Encoder::encode_int_max(const BasicVar& a, const BasicVar& b, const BasicVar& c, CNF& cnf_clauses){

    if(export_proof){
        
        isLIA = true;
        
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *c.name << " (ite (>= " << *a.name << " " <<
                                        *b.name << ") " << *a.name << " " << *b.name << "))\n)\n";
    }

    if(!encode_primitive_comparison_minus(a, c, 0, cnf_clauses)){
        declare_unsat(cnf_clauses);
        return;
    }
    if(!encode_primitive_comparison_minus(b, c, 0, cnf_clauses)){
        declare_unsat(cnf_clauses);
        return;
    }

    Clause temp_clause;
    CNF temp_clauses;
    if(export_proof){
        export_proof = false;
        encode_primitive_comparison_minus(c, a, 0, temp_clauses);
        export_proof = true;
    } else 
        encode_primitive_comparison_minus(c, a, 0, temp_clauses);

    if(!temp_clauses.empty()){
        int id1 = next_helper_id++;
        LiteralPtr helper1 = make_literal(LiteralType::HELPER, id1, true, 0);
        temp_clause.push_back(helper1);

        for(int i = 0; i < (int)temp_clauses.size(); i++){
            if(export_proof){
                helper_map[helper1->id].push_back(temp_clauses[i]);
            }

            temp_clauses[i].push_back(make_literal(LiteralType::HELPER, id1, false, 0));
        }    

        for(auto clause : temp_clauses){
            cnf_clauses.push_back(clause);

            if(export_proof)
                sat_constraint_clauses.push_back(clause);
        }
    }

    temp_clauses.clear();
    if(export_proof){
        export_proof = false;
        encode_primitive_comparison_minus(c, b, 0, temp_clauses);
        export_proof = true;
    } else 
        encode_primitive_comparison_minus(c, b, 0, temp_clauses);

    if(!temp_clauses.empty()){
        int id2 = next_helper_id++;
        LiteralPtr helper2 = make_literal(LiteralType::HELPER, id2, true, 0);
        temp_clause.push_back(helper2);

        for(int i = 0; i < (int)temp_clauses.size(); i++){
            if(export_proof){
                helper_map[helper2->id].push_back(temp_clauses[i]);
            }
        
            temp_clauses[i].push_back(make_literal(LiteralType::HELPER, id2, false, 0));
        }

        for(auto clause : temp_clauses){
            cnf_clauses.push_back(clause);

            if(export_proof)
                sat_constraint_clauses.push_back(clause);
        }            
    }


    temp_clauses.push_back(temp_clause);
    if(export_proof){
        definition_clauses.push_back(temp_clause);
        sat_constraint_clauses.push_back(temp_clause);
    }
    cnf_clauses.insert(cnf_clauses.end(), temp_clauses.begin(), temp_clauses.end());

}

// Encodes a constraint of type min(a, b) = c
void Encoder::encode_int_min(const BasicVar& a, const BasicVar& b, const BasicVar& c, CNF& cnf_clauses){
    
    if(export_proof){
        
        isLIA = true;
        
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *c.name << " (ite (<= " << *a.name << " " <<
                                        *b.name << ") " << *a.name << " " << *b.name << "))\n)\n";
    }

    if(!encode_primitive_comparison_minus(c, a, 0, cnf_clauses)){
        declare_unsat(cnf_clauses);
        return;
    }
    if(!encode_primitive_comparison_minus(c, b, 0, cnf_clauses)){
        declare_unsat(cnf_clauses);
        return;
    }

    Clause temp_clause;
    CNF temp_clauses;
    if(export_proof){
        export_proof = false;
        encode_primitive_comparison_minus(a, c, 0, temp_clauses);
        export_proof = true;
    } else 
        encode_primitive_comparison_minus(a, c, 0, temp_clauses);

    if(!temp_clauses.empty()){
        int id1 = next_helper_id++;
        LiteralPtr helper1 = make_literal(LiteralType::HELPER, id1, true, 0);
        temp_clause.push_back(helper1);

        for(int i = 0; i < (int)temp_clauses.size(); i++){
            if(export_proof){
                helper_map[helper1->id].push_back(temp_clauses[i]);
            }

            temp_clauses[i].push_back(make_literal(LiteralType::HELPER, id1, false, 0));
        }    

        for(auto clause : temp_clauses){
            cnf_clauses.push_back(clause);

            if(export_proof)
                sat_constraint_clauses.push_back(clause);
        }
    }

    temp_clauses.clear();
    if(export_proof){
        export_proof = false;
        encode_primitive_comparison_minus(b, c, 0, temp_clauses);
        export_proof = true;
    } else 
        encode_primitive_comparison_minus(b, c, 0, temp_clauses);

    if(!temp_clauses.empty()){
        int id2 = next_helper_id++;
        LiteralPtr helper2 = make_literal(LiteralType::HELPER, id2, true, 0);
        temp_clause.push_back(helper2);

        for(int i = 0; i < (int)temp_clauses.size(); i++){
            if(export_proof){
                helper_map[helper2->id].push_back(temp_clauses[i]);
            }
        
            temp_clauses[i].push_back(make_literal(LiteralType::HELPER, id2, false, 0));
        }

        for(auto clause : temp_clauses){
            cnf_clauses.push_back(clause);

            if(export_proof)
                sat_constraint_clauses.push_back(clause);
        }            
    }


    temp_clauses.push_back(temp_clause);
    if(export_proof){
        definition_clauses.push_back(temp_clause);
        sat_constraint_clauses.push_back(temp_clause);
    }
    cnf_clauses.insert(cnf_clauses.end(), temp_clauses.begin(), temp_clauses.end());


}

// Encodes a constraint of type a % b = c
void Encoder::encode_int_mod(const BasicVar& a, const BasicVar& b, const BasicVar& c, CNF& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    if(b_left == 0 && b_right == 0){
        if(export_proof){
            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n false\n)\n";
        }

        declare_unsat(cnf_clauses);
        return;
    }

    if(b_left <= 0 && b_right >= 0){
        LiteralPtr l1 = make_literal(LiteralType::ORDER, b.id, true, -1);
        LiteralPtr l2 = make_literal(LiteralType::ORDER, b.id, false, 0);
        cnf_clauses.push_back({l1, l2});

        if(export_proof){
            sat_constraint_clauses.push_back({l1, l2});
        }
    }

    if(b_left == 0)
        b_left = 1;
    else if(b_right == 0)
        b_right = -1;

    int p_left = a_left/b_left, p_right = a_left/b_left;
    for(int i = a_left; i <= a_right; i++)  
        for(int j = b_left; j <= b_right; j++){
            if(j == 0) continue;
            if(i/j < p_left)
                p_left = i/j;
            if(i/j > p_right)
                p_right = i/j;
        }

    BasicVar* p = encode_int_range_helper_variable(p_left, p_right, cnf_clauses, true);
    int bp_left = min({b_left*p_left, b_left*p_right, b_right*p_left, b_right*p_right});
    int bp_right = max({b_left*p_left, b_left*p_right, b_right*p_left, b_right*p_right});
    BasicVar* bp = encode_int_range_helper_variable(bp_left, bp_right, cnf_clauses, true); 
    
    if(export_proof){
        CNF temp_clauses;
        export_proof = false;
        encode_int_times(b, *p, *bp, temp_clauses);
        for(auto c : temp_clauses){
            sat_constraint_clauses.push_back(c);
            cnf_clauses.push_back(c);
        }
        export_proof = true;
    } else 
        encode_int_times(b, *p, *bp, cnf_clauses);
        

    int c_abs_left = c_left*c_right < 0 ? 0 : min(abs(c_left), abs(c_right));
    int c_abs_right = max(abs(c_left), abs(c_right));
    BasicVar* c_abs = encode_int_range_helper_variable(c_abs_left, c_abs_right, cnf_clauses, true);

    int b_abs_left = b_left*b_right < 0 ? 0 : min(abs(b_left), abs(b_right));
    int b_abs_right = max(abs(b_left), abs(b_right));
    BasicVar* b_abs = encode_int_range_helper_variable(b_abs_left, b_abs_right, cnf_clauses, true);

    if(export_proof){
        export_proof = false;

        CNF temp_clauses;
        encode_int_abs(c, *c_abs, temp_clauses);
        encode_int_abs(b, *b_abs, temp_clauses);
        encode_int_lt(*c_abs, *b_abs, temp_clauses);
        encode_int_plus(*bp, c, a, temp_clauses);
        export_proof = true;

        for(auto& clause : temp_clauses){
            cnf_clauses.push_back(clause);

            if(export_proof){
                Clause new_clause;
                bool is_definition = true;
                int lit_id = -1;
                for(auto& lit : clause){
                    if(lit->type != LiteralType::HELPER){
                        is_definition = false;
                        new_clause.push_back(lit);
                    } else
                        lit_id = lit->id;
                }

                if(is_definition)
                    definition_clauses.push_back(clause);
                else if(lit_id != -1)
                    helper_map[lit_id].push_back(new_clause);

                sat_constraint_clauses.push_back(clause);    
            }
        }
    } else {
        encode_int_abs(c, *c_abs, cnf_clauses);
        encode_int_abs(b, *b_abs, cnf_clauses);
        encode_int_lt(*c_abs, *b_abs, cnf_clauses);
        encode_int_plus(*bp, c, a, cnf_clauses);       
    } 

    if(export_proof){
        
        is2step = true;
        isNIA = true;
        needModDiv = true;

        constraint2step_set.insert(next_constraint_num);

        constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
        constraints2step1 << "(and\n";
        constraints2step1 << "(mzn_mod " << *a.name << " " << *b.name << " " << *c.name << ")\n";
        constraints2step1 << "(ite (< " << *a.name << " 0) (<= " << *c.name << " 0) (>= " << *c.name << " 0))\n";

        constraints2step1 << "(not (= " << *b.name << " 0))\n)\n)\n";


        connection2step << "(= " << *bp->name << " (* " << *b.name << " " << *p->name << "))\n";
        connection2step << "(= " << *c_abs->name << " (ite (<= 0 " << *c.name << ") " 
                                     << *c.name << " (- " << *c.name << ")))\n";
        connection2step << "(= " << *b_abs->name << " (ite (<= 0 " << *b.name << ") " 
                                     << *b.name << " (- " << *b.name << ")))\n";
        connection2step << "(mzn_div " << *a.name << " " << *b.name << " " << *p->name << ")\n"; 
        connection2step << "---" << endl;

        smt_step1_funs << "(define-fun f_" << *bp->name << " () Int\n";
        smt_step1_funs << "(* " << *b.name << " " << *p->name << ")\n)\n";
        smt_step1_funs << "(define-fun f_" << *c_abs->name << " () Int\n";
        smt_step1_funs << "(ite (<= 0 " << *c.name << ") " << *c.name << " (- " << *c.name << ")))\n";
        smt_step1_funs << "(define-fun f_" << *b_abs->name << " () Int\n";
        smt_step1_funs << "(ite (<= 0 " << *b.name << ") " << *b.name << " (- " << *b.name << ")))\n";
        smt_step1_funs << "(define-fun f_" << *p->name << " () Int\n";
        smt_step1_funs << "(mzn_div_f " << *a.name << " " << *b.name << ")\n)\n";

        smt_subspace_step1 << "!(distinct " << *b.name << " 0)\n---\n";

        left_total_step1 << "(= " << *bp->name << " f_" << *bp->name << ")\n"; 
        left_total_step1 << "(= " << *c_abs->name << " f_" << *c_abs->name << ")\n"; 
        left_total_step1 << "(= " << *b_abs->name << " f_" << *b_abs->name << ")\n"; 
        left_total_step1 << "(= " << *p->name << " f_" << *p->name << ")\n"; 

        constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        constraints2step2 << "(and\n";
        constraints2step2 << "(= " << *bp->name << " (* " <<
                                     *b.name << " " << *p->name << "))\n";
        constraints2step2 << "(= " << *c_abs->name << " (ite (>= " <<
                                     *c.name << " 0) " << *c.name << " (- " << *c.name <<
                                    ")))\n";
        constraints2step2 << "(= " << *b_abs->name << " (ite (>= " <<
                                     *b.name << " 0) " << *b.name << " (- " << *b.name <<
                                    ")))\n";
        constraints2step2 << "(< " << *c_abs->name << " " << *b_abs->name << ")\n";

        constraints2step2 << "(ite (< " << *a.name << " 0) (<= " << *c.name << " 0) (>= " << *c.name << " 0))\n";

        constraints2step2 << "(= " << *a.name << " (+ " <<
                                     *c.name << " " << *bp->name << "))\n)\n)\n";
    }

    LiteralPtr pos_c = make_literal(LiteralType::ORDER, c.id, false, -1);
    LiteralPtr neg_c = make_literal(LiteralType::ORDER, c.id, true, 0);

    if(a_right < 0){
        if(c_left > 0){
            declare_unsat(cnf_clauses);
            return;
        } else if(c_right >= 0){
            cnf_clauses.push_back({neg_c});

            if(export_proof)
                sat_constraint_clauses.push_back({neg_c});
        }
    } else if(a_left > 0){
        if(c_right < 0){
            declare_unsat(cnf_clauses);
            return;
        } else if(c_left <= 0){
            cnf_clauses.push_back({pos_c});

            if(export_proof)
                sat_constraint_clauses.push_back({pos_c});
        }
    } else {

        if(c_right > 0)
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, true, -1),
                                pos_c});
        else
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, true, -1)});    

        if(c_left < 0)
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, false, 0),
                                   neg_c}); 
        else
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, a.id, false, 0)});

        if(export_proof){

            if(c_left < 0)
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, a.id, true, -1),
                                    pos_c});
            else
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, a.id, true, -1)});  

            if(c_right > 0)
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, a.id, false, 0),
                                    neg_c});
            else
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, a.id, false, 0)});
        }
    }


}

// TODO proveri prvo granice
// Encodes a constraint of type a =/= b
void Encoder::encode_int_ne(const BasicVar& a, const BasicVar& b, CNF& cnf_clauses){

    if(export_proof){
        
        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(distinct " << *a.name << " " << *b.name << ")\n)\n";
    }

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);

    if(a_left == b_right && a_right == b_left){
        declare_unsat(cnf_clauses);
    } else if(a_right >= b_left && a_left <= b_right){

        Clause helper_clause;

        CNF temp_clauses; 
        if(export_proof){
            export_proof = false;
            encode_primitive_comparison_minus(a, b, -1, temp_clauses);
            export_proof = true;
        } else {
            encode_primitive_comparison_minus(a, b, -1, temp_clauses);
        }

        if(!temp_clauses.empty()){
            int id1 = next_helper_id++;
            LiteralPtr helper1 = make_literal(LiteralType::HELPER, id1, true, 0);
            helper_clause.push_back(helper1);

            if(export_proof)
                for(auto clause : temp_clauses)
                    helper_map[id1].push_back(clause);

            for(int i = 0; i < (int)temp_clauses.size(); i++)
                temp_clauses[i].push_back(make_literal(LiteralType::HELPER, id1, false, 0));

            for(auto clause : temp_clauses){
                cnf_clauses.push_back(clause);

                if(export_proof)
                    sat_constraint_clauses.push_back(clause);
            }
        }

        temp_clauses.clear();
        
        if(export_proof){
            export_proof = false;
            encode_primitive_comparison_minus(b, a, -1, temp_clauses);
            export_proof = true;
        } else {
            encode_primitive_comparison_minus(b, a, -1, temp_clauses);
        }
        
        if(!temp_clauses.empty()){
            int id2 = next_helper_id++;
            LiteralPtr helper2 = make_literal(LiteralType::HELPER, id2, true, 0);
            helper_clause.push_back(helper2);
            
            if(export_proof)
                for(auto clause : temp_clauses)
                    helper_map[id2].push_back(clause);

            for(int i = 0; i < (int)temp_clauses.size(); i++)
                temp_clauses[i].push_back(make_literal(LiteralType::HELPER, id2, false, 0));

            for(auto clause : temp_clauses){
                cnf_clauses.push_back(clause);

                if(export_proof)
                    sat_constraint_clauses.push_back(clause);
            }
        }

        cnf_clauses.push_back(helper_clause);

        if(export_proof){
            definition_clauses.push_back(helper_clause);
            sat_constraint_clauses.push_back(helper_clause);
        }

    } else {
        LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        cnf_clauses.push_back({yes_helper, not_helper});

        if(export_proof){
            sat_constraint_clauses.push_back({yes_helper, not_helper});
        }
    }


}

// Encodes a constraint of type (a =/= b) <-> r
void Encoder::encode_int_ne_reif(const BasicVar& a, const BasicVar& b, const BasicVar& r, CNF& cnf_clauses){

    if(export_proof){
        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (distinct " << *a.name << " " << *b.name 
                                     << ") 1 0))\n)\n"; 
    }

    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    if(get_left(&a) > get_right(&b) || get_right(&a) < get_left(&b)){
        cnf_clauses.push_back({yes_r});

        if(export_proof)
            sat_constraint_clauses.push_back({yes_r});

        return;
    }


    LiteralPtr yes_r1 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
    LiteralPtr not_r1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    LiteralPtr yes_r2 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
    LiteralPtr not_r2 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    
    CNF temp_clauses1;
    CNF temp_clauses2;

    if(export_proof){
        export_proof = false;
        
        encode_int_lt(a, b, temp_clauses1);
        encode_int_lt(b, a, temp_clauses2);
    
        export_proof = true;
    } else {
        encode_int_lt(a, b, temp_clauses1);
        encode_int_lt(b, a, temp_clauses2);
    }

    reify_helper(temp_clauses1, yes_r1, cnf_clauses);
    reify_helper(temp_clauses2, yes_r2, cnf_clauses);

    cnf_clauses.push_back({yes_r, not_r1});
    cnf_clauses.push_back({yes_r, not_r2});
    cnf_clauses.push_back({not_r, yes_r1, yes_r2});

    if(export_proof){
        
        sat_constraint_clauses.push_back({yes_r, not_r1});
        sat_constraint_clauses.push_back({yes_r, not_r2});
        sat_constraint_clauses.push_back({not_r, yes_r1, yes_r2});

        definition_clauses.push_back({yes_r, not_r1});
        definition_clauses.push_back({yes_r, not_r2});
        definition_clauses.push_back({not_r, yes_r1, yes_r2});        
    }

}

// Encodes a constraint of type r -> (a =/= b)
void Encoder::encode_int_ne_imp(const BasicVar& a, const BasicVar& b, const BasicVar& r, CNF& cnf_clauses){


    if(export_proof){
        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (distinct " << *a.name << " " << *b.name 
                                     << "))\n)\n"; 
    }


    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    if(get_left(&a) > get_right(&b) || get_right(&a) < get_left(&b)){
        cnf_clauses.push_back({yes_r, not_r});

        if(export_proof)
            sat_constraint_clauses.push_back({yes_r, not_r});
        return;
    }

    LiteralPtr yes_r1 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
    LiteralPtr not_r1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    LiteralPtr yes_r2 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
    LiteralPtr not_r2 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    
    CNF temp_clauses1;
    CNF temp_clauses2;

    if(export_proof){
        export_proof = false;
        
        encode_int_lt(a, b, temp_clauses1);
        encode_int_lt(b, a, temp_clauses2);
    
        export_proof = true;
    } else {
        encode_int_lt(a, b, temp_clauses1);
        encode_int_lt(b, a, temp_clauses2);
    }

    reify_helper(temp_clauses1, yes_r1, cnf_clauses);
    reify_helper(temp_clauses2, yes_r2, cnf_clauses);

    cnf_clauses.push_back({yes_r, not_r1});
    cnf_clauses.push_back({yes_r, not_r2});
    cnf_clauses.push_back({not_r, yes_r1, yes_r2});

    if(export_proof){
        
        sat_constraint_clauses.push_back({not_r, yes_r1, yes_r2});

        definition_clauses.push_back({not_r, yes_r1, yes_r2});        
    }

}

// Encodes a constraint of type a + b = c
void Encoder::encode_int_plus(const BasicVar& a, const BasicVar& b, const BasicVar& c, CNF& cnf_clauses){

    if(export_proof){
        
        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *c.name << " (+ " <<
                                     *a.name << " " << *b.name << "))\n)\n";
    }


    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    if(a_left + b_left > c_right || a_right + b_right < c_left){
        declare_unsat(cnf_clauses);
        return;
    }

    Clause new_clause;

    //-c + a + b <= 0
    for(int i = -c_right - 1; i <= -c_left; i++){
        for(int j = a_left - 1; j <= a_right; j++){
            for(int k = b_left - 1; k <= b_right; k++){
                if(i + j + k == -2){
                    
                    new_clause.push_back(make_literal(LiteralType::ORDER, c.id, false, -i - 1));
                    new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, j));
                    new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, k));

                    cnf_clauses.push_back(new_clause);

                    if(export_proof)
                        sat_constraint_clauses.push_back(new_clause);

                    new_clause.clear();
                }
            }
        }
    }    

    //c - a - b <= 0
    for(int i = c_left - 1; i <= c_right; i++){
        for(int j = -a_right - 1; j <= -a_left; j++){
            for(int k = -b_right - 1; k <= -b_left; k++){
                if(i + j + k == -2){

                    new_clause.push_back(make_literal(LiteralType::ORDER, c.id, true, i));
                    new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, -j - 1)); 
                    new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, -k - 1));                         
                
                    cnf_clauses.push_back(new_clause);

                    if(export_proof)
                        sat_constraint_clauses.push_back(new_clause);                    

                    new_clause.clear();
                }
            }
        }
    }

}

// Encodes a constraint of type a^b = c
void Encoder::encode_int_pow(const BasicVar& a, const BasicVar& b, const BasicVar& c, CNF& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    if(export_proof){
        isNIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(and\n";
        trivial_encoding_constraints << "(<= 0 " << *b.name << ")\n";
        
        trivial_encoding_constraints << "(= " << *c.name << "\n";
        for(int i = 0; i <= b_right; i++){
            if(i == 0)
                trivial_encoding_constraints << "(ite (= " << *b.name << " 0) 1\n";
            else if(i == 1)
                trivial_encoding_constraints << "(ite (= " << *b.name << " " << "1) " << *a.name << "\n";
            else {
                trivial_encoding_constraints << "(ite (= " << *b.name << " "  << i << ") (* ";
                for(int j = 0; j < i; j++)
                    trivial_encoding_constraints << *a.name << " ";
                trivial_encoding_constraints << ")\n";
            }  
        }
        trivial_encoding_constraints << " 0";

        for(int i = 0; i <= b_right + 1; i++)
            trivial_encoding_constraints << ")";
        trivial_encoding_constraints << "\n)\n)\n";
    }


    if(b_right < 0){
        declare_unsat(cnf_clauses);
        return;
    } else if(b_left < 0){
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1)});
    }

    encode_direct(a, cnf_clauses);
    encode_direct(b, cnf_clauses);
    encode_direct(c, cnf_clauses);

    Clause helpers;
    for(int i = a_left; i <= a_right; i++)
        for(int j = b_left; j <= b_right; j++){
            if(pow(i, j) >= c_left && pow(i, j) <= c_right){
                LiteralPtr helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
                helpers.push_back(make_literal(LiteralType::HELPER, helper->id, true, 0));
                Clause new_clause1 = {helper, make_literal(LiteralType::DIRECT, a.id, true, i)};
                Clause new_clause2 = {helper, make_literal(LiteralType::DIRECT, b.id, true, j)};
                Clause new_clause3 = {helper, make_literal(LiteralType::DIRECT, c.id, true, pow(i, j))};
                cnf_clauses.push_back(new_clause1);
                cnf_clauses.push_back(new_clause2);
                cnf_clauses.push_back(new_clause3);

                if(export_proof){
                    helper_map[helper->id].push_back({make_literal(LiteralType::DIRECT, a.id, true, i)});
                    helper_map[helper->id].push_back({make_literal(LiteralType::DIRECT, b.id, true, j)});
                    helper_map[helper->id].push_back({make_literal(LiteralType::DIRECT, c.id, true, pow(i, j))});

                    sat_constraint_clauses.push_back(new_clause1);
                    sat_constraint_clauses.push_back(new_clause2);
                    sat_constraint_clauses.push_back(new_clause3);                    
                }
            }
        }

    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }
}

// Encodes a constraint of type a * b = c, where all domains are nonnegative
void Encoder::encode_int_times_nonnegative(const BasicVar& a, const BasicVar& b, const BasicVar& c, CNF& cnf_clauses){

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    Clause new_clause;
    for(int i = a_left; i <= a_right; i++){
        for(int j = b_left; j <= b_right; j++){
            if(i*j >= c_right)
                continue;
            else if(i*j < c_left){
                new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, i));
                new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, j));
            } else {
                new_clause.push_back(make_literal(LiteralType::ORDER, c.id, true, i*j));
                new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, i));
                new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, j));
            }
            cnf_clauses.push_back(new_clause);

            if(export_proof)
                sat_constraint_clauses.push_back(new_clause);
            new_clause.clear();
        }
    }

    for(int i = a_left; i <= a_right; i++){
        for(int j = b_left; j <= b_right; j++){
            if(i*j <= c_left)
                continue;
            else if(i*j > c_right){
                new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, i - 1));
                new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, j - 1));
            } else {
                new_clause.push_back(make_literal(LiteralType::ORDER, c.id, false, i*j - 1));
                new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, i - 1));
                new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, j - 1));
            }
            cnf_clauses.push_back(new_clause);

            if(export_proof)
                sat_constraint_clauses.push_back(new_clause);
            new_clause.clear();
        }
    }

}

// Encodes a constraint of type a * b = c
void Encoder::encode_int_times(const BasicVar& a, const BasicVar& b, const BasicVar& c, CNF& cnf_clauses){

    if(export_proof){
        
        isNIA = true;
        
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *c.name << " (* " <<
                                     *a.name << " " << *b.name << "))\n)\n";
    }

    int a_left = get_left(&a);
    int a_right = get_right(&a);
    int b_left = get_left(&b);
    int b_right = get_right(&b);
    int c_left = get_left(&c);
    int c_right = get_right(&c);

    if(a_left >= 0 && b_left >= 0 && c_left >= 0){

        encode_int_times_nonnegative(a, b, c, cnf_clauses);
        return;
    }

    for(int ma = a_left; ma <= a_right; ma++){
        for(int Ma = ma; Ma <= a_right; Ma++){
            for(int mb = b_left; mb <= b_right; mb++){
                for(int Mb = mb; Mb <= b_right; Mb++){
                    int curr_max = max({ma*mb, ma*Mb, Ma*mb, Ma*Mb});
                    Clause new_clause;

                    if(c_right <= curr_max)
                        continue;
                    else if(c_left > curr_max){
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, Mb));
                    } else {
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, Mb));
                        new_clause.push_back(make_literal(LiteralType::ORDER, c.id, true, curr_max));
                    }

                    cnf_clauses.push_back(new_clause);

                    if(export_proof)
                        sat_constraint_clauses.push_back(new_clause);
                }
            }
        } 
    }

    for(int ma = a_left; ma <= a_right; ma++){
        for(int Ma = ma; Ma <= a_right; Ma++){
            for(int mb = b_left; mb <= b_right; mb++){
                for(int Mb = mb; Mb <= b_right; Mb++){
                    int curr_min = min({ma*mb, ma*Mb, Ma*mb, Ma*Mb});
                    Clause new_clause;

                    if(c_left >= curr_min)
                        continue;
                    else if(c_right < curr_min){
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, Mb));
                    } else {
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, true, ma - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, a.id, false, Ma));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, true, mb - 1));
                        new_clause.push_back(make_literal(LiteralType::ORDER, b.id, false, Mb));
                        new_clause.push_back(make_literal(LiteralType::ORDER, c.id, false, curr_min - 1));                        
                    }

                    cnf_clauses.push_back(new_clause);

                    if(export_proof)
                        sat_constraint_clauses.push_back(new_clause);
                }
            }
        } 
    }

}

// Encodes a constraint of type x ∈ S1
void Encoder::encode_set_in(const BasicVar& x, const BasicLiteralExpr& S1, CNF &cnf_clauses){
    
    auto S = get<SetLiteral*>(S1);
    auto left = get_left(&x);
    auto right = get_right(&x);

    vector<int> elems;
    if(holds_alternative<SetSetLiteral*>(*S)){
        elems = *get<SetSetLiteral*>(*S)->elems;
    } else {
        int left = get<SetRangeLiteral*>(*S)->left;
        int right = get<SetRangeLiteral*>(*S)->right;
        for(int i = left; i <= right; i++)
            elems.push_back(i);
    }

    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        if(elems.size() > 1)
            trivial_encoding_constraints << "(or ";
        for(auto elem : elems){
            trivial_encoding_constraints << "(= " << *x.name << " " << elem << ") ";
        }
        if(elems.size() > 1)
            trivial_encoding_constraints << ")";
        trivial_encoding_constraints << "\n)\n";
    }

    if(left > elems[elems.size() - 1] || right < elems[0]){
        declare_unsat(cnf_clauses);
        return ;
    }

    Clause helpers;
    for(auto elem : elems){
        LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        if(elem >= left && elem <= right){
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, elem),
                                    not_helper});
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, elem-1),
                                    not_helper});

            if(export_proof){
                helper_map[not_helper->id].push_back({make_literal(LiteralType::ORDER, x.id, true, elem)});
                helper_map[not_helper->id].push_back({make_literal(LiteralType::ORDER, x.id, false, elem-1)});
                
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, elem),
                                        not_helper});
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, elem-1),
                                        not_helper});
            }
            
            helpers.push_back(yes_helper);
        }
    }

    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }
}

// ---------------------------- Encoding Bool constraints -------------------------------------

// Encodes a constraint of type r ↔ ⋀i as[i]
void Encoder::encode_array_bool_and(const ArrayLiteral& as, const BasicVar& r, CNF& cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (= " << as.size() << " (+ ";

        for(int i = 0; i < (int)as.size(); i++){
            auto var = get_var_from_array(as, i);
            trivial_encoding_constraints << *var->name << " ";
        }

        trivial_encoding_constraints << ")) 1 0))\n)\n";
        
    }


    Clause new_clause1;
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    for(int i = 0; i < (int)as.size(); i++){
        auto p = get_var_from_array(as, i);

        LiteralPtr not_p = make_literal(LiteralType::BOOL_VARIABLE, p->id, false, 0);
        LiteralPtr yes_p = make_literal(LiteralType::BOOL_VARIABLE, p->id, true, 0); 

        new_clause1.push_back(not_p);

        Clause new_clause2 = {yes_p, not_r};
        cnf_clauses.push_back(new_clause2);

        if(export_proof)
            sat_constraint_clauses.push_back(new_clause2);

    }

    new_clause1.push_back(yes_r);
    cnf_clauses.push_back(new_clause1);

    if(export_proof)
        sat_constraint_clauses.push_back(new_clause1);

}

// Encodes a constraint of type as[b] = c, where as is an array of bool parameters
void Encoder::encode_array_bool_element(const BasicVar& b, const ArrayLiteral& as, BasicVar& c, CNF& cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(and\n";
        trivial_encoding_constraints << "(<= 1 " << *b.name << " " << as.size() << ")\n";
        trivial_encoding_constraints << "(= " << *c.name << "\n";
        for(int i = 0; i < (int)as.size(); i++){
            auto elem = get_bool_from_array(as, i);
            string elem_string = (elem == false) ? "0" : "1";
            trivial_encoding_constraints << "(ite (= " << *b.name << " " << i + 1 << ") " << elem_string << "\n";
        }
        trivial_encoding_constraints << "-1" << endl;
        for(int i = 0; i < (int)as.size() + 2; i++)
            trivial_encoding_constraints << ")";
        
        trivial_encoding_constraints << ")\n";
        
    }


    int b_left = get_left(&b);
    int b_right = get_right(&b);

    Clause helpers;  
    Clause new_clause1, new_clause2;
    for(int i = b_left; i <= b_right; i++){
        if(i < 1 || i > (int)as.size())
            continue;
        
        LiteralPtr helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        new_clause1 = { make_literal(LiteralType::ORDER, b.id, true, i), helper};
        new_clause2 = { make_literal(LiteralType::ORDER, b.id, false, i-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);

        if(export_proof){
            helper_map[helper->id].push_back({make_literal(LiteralType::ORDER, b.id, true, i)});
            helper_map[helper->id].push_back({make_literal(LiteralType::ORDER, b.id, false, i-1)});

            sat_constraint_clauses.push_back(new_clause1);
            sat_constraint_clauses.push_back(new_clause2);
        }

        bool curr_elem = get_bool_from_array(as, i-1);

        new_clause1 = { make_literal(LiteralType::BOOL_VARIABLE, c.id, curr_elem ? true : false, 0), helper};
        cnf_clauses.push_back(new_clause1);

        if(export_proof){
            helper_map[helper->id].push_back({make_literal(LiteralType::BOOL_VARIABLE, c.id, curr_elem ? true : false, 0)});

            sat_constraint_clauses.push_back(new_clause1);
        }       

        LiteralPtr not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }
    
    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }

}

// Encodes a constraint of type r ↔ ⋁i as[i]
void Encoder::encode_array_bool_or(const ArrayLiteral& as, const BasicVar& r, CNF& cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (<= 1 (+ ";

        for(int i = 0; i < (int)as.size(); i++){
            auto var = get_var_from_array(as, i);
            trivial_encoding_constraints << *var->name << " ";
        }

        trivial_encoding_constraints << ")) 1 0))\n)\n";
        
    }

    Clause new_clause1;
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    for(int i = 0; i < (int)as.size(); i++){
        auto p = get_var_from_array(as, i);
        LiteralPtr not_p = make_literal(LiteralType::BOOL_VARIABLE, p->id, false, 0);
        LiteralPtr yes_p = make_literal(LiteralType::BOOL_VARIABLE, p->id, true, 0); 

        new_clause1.push_back(yes_p);

        Clause new_clause2 = {not_p, yes_r};
        cnf_clauses.push_back(new_clause2);

        if(export_proof)
            sat_constraint_clauses.push_back(new_clause2);
    }

    new_clause1.push_back(not_r);
    cnf_clauses.push_back(new_clause1);

    if(export_proof)
        sat_constraint_clauses.push_back(new_clause1);
}

// Encodes a constraint of type xor i as[i]
void Encoder::encode_array_bool_xor(const ArrayLiteral& as, CNF& cnf_clauses){
    

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= 1 (mod (+ ";

        for(int i = 0; i < (int)as.size(); i++){
            auto var = get_var_from_array(as, i);
            trivial_encoding_constraints << *var->name  << " ";
        }

        trivial_encoding_constraints << ") 2))\n)\n";
        
    }    

    auto var0 = get_var_from_array(as, 0);
    auto var1 = get_var_from_array(as, 1);
    if(as.size() == 2){
        encode_bool_xor(*var0, *var1, cnf_clauses);
        return;
    }

    LiteralPtr yes_var0 = make_literal(LiteralType::BOOL_VARIABLE, var0->id, true, 0);
    LiteralPtr yes_var1 = make_literal(LiteralType::BOOL_VARIABLE, var1->id, true, 0);
    LiteralPtr yes_r = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
    LiteralPtr not_var0 = make_literal(LiteralType::BOOL_VARIABLE, var0->id, false, 0);
    LiteralPtr not_var1 = make_literal(LiteralType::BOOL_VARIABLE, var1->id, false, 0);
    LiteralPtr not_r = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

    cnf_clauses.push_back({yes_r, not_var0, yes_var1});
    cnf_clauses.push_back({yes_r, yes_var0, not_var1});
    cnf_clauses.push_back({not_r, yes_var0, yes_var1});
    cnf_clauses.push_back({not_r, not_var0, not_var1});

    if(export_proof){
        helper_map[yes_r->id].push_back({yes_var0, yes_var1});
        helper_map[yes_r->id].push_back({not_var0, not_var1});
        helper_map[-yes_r->id].push_back({not_var0, yes_var1});
        helper_map[-yes_r->id].push_back({yes_var0, not_var1});        

        sat_constraint_clauses.push_back({yes_r, not_var0, yes_var1});
        sat_constraint_clauses.push_back({yes_r, yes_var0, not_var1});  
        sat_constraint_clauses.push_back({not_r, yes_var0, yes_var1});
        sat_constraint_clauses.push_back({not_r, not_var0, not_var1});
    }

    for(int i = 2; i < (int)as.size() - 1; i++){
        auto var_i = get_var_from_array(as, i);
        LiteralPtr yes_var_i = make_literal(LiteralType::BOOL_VARIABLE, var_i->id, true, 0);
        LiteralPtr yes_r0 = make_literal(LiteralType::HELPER, next_helper_id-1, true, 0);
        LiteralPtr yes_r1 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        LiteralPtr not_var_i = make_literal(LiteralType::BOOL_VARIABLE, var_i->id, false, 0);
        LiteralPtr not_r0 = make_literal(LiteralType::HELPER, next_helper_id-1, false, 0);
        LiteralPtr not_r1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
    
        cnf_clauses.push_back({yes_r1, not_var_i, yes_r0});
        cnf_clauses.push_back({yes_r1, yes_var_i, not_r0});
        cnf_clauses.push_back({not_r1, yes_var_i, yes_r0});
        cnf_clauses.push_back({not_r1, not_var_i, not_r0});

        if(export_proof){
            helper_map[not_r1->id].push_back({yes_var_i, yes_r0});
            helper_map[not_r1->id].push_back({not_var_i, not_r0});
            helper_map[-not_r1->id].push_back({not_var_i, yes_r0});
            helper_map[-not_r1->id].push_back({yes_var_i, not_r0});

            sat_constraint_clauses.push_back({yes_r1, not_var_i, yes_r0});
            sat_constraint_clauses.push_back({yes_r1, yes_var_i, not_r0});
            sat_constraint_clauses.push_back({not_r1, yes_var_i, yes_r0});
            sat_constraint_clauses.push_back({not_r1, not_var_i, not_r0});
        }
        
    }

    auto var_n = get_var_from_array(as, as.size() - 1);
    LiteralPtr yes_var_n = make_literal(LiteralType::BOOL_VARIABLE, var_n->id, true, 0);
    LiteralPtr yes_r_n = make_literal(LiteralType::HELPER, next_helper_id-1, true, 0);
    LiteralPtr not_var_n = make_literal(LiteralType::BOOL_VARIABLE, var_n->id, false, 0);
    LiteralPtr not_r_n = make_literal(LiteralType::HELPER, next_helper_id-1, false, 0);

    cnf_clauses.push_back({yes_var_n, yes_r_n});
    cnf_clauses.push_back({not_var_n, not_r_n});

    if(export_proof){
        sat_constraint_clauses.push_back({yes_var_n, yes_r_n});
        sat_constraint_clauses.push_back({not_var_n, not_r_n});

        definition_clauses.push_back({yes_var_n, yes_r_n});
        definition_clauses.push_back({not_var_n, not_r_n});
    }

}

// Encodes a constraint of type as[b] = c, where as is an array of bool var parameters
void Encoder::encode_array_var_bool_element(const BasicVar& b, const ArrayLiteral& as, BasicVar& c, CNF& cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(and\n";
        trivial_encoding_constraints << "(<= 1 " << *b.name << " " << as.size() << ")\n";
        trivial_encoding_constraints << "(= " << *c.name << "\n";
        for(int i = 0; i < (int)as.size(); i++){
            auto var = get_var_from_array(as, i);
            trivial_encoding_constraints << "(ite (= " << *b.name << " " << i + 1 << ") " << *var->name << "\n";
        }
        trivial_encoding_constraints << "-1" << endl;
        for(int i = 0; i < (int)as.size() + 2; i++)
            trivial_encoding_constraints << ")";
        
        trivial_encoding_constraints << ")\n";
    }

    int b_left = get_left(&b);
    int b_right = get_right(&b);
    
    Clause helpers;  
    Clause new_clause1, new_clause2;
    for(int i = b_left; i <= b_right; i++){
        if(i < 1 || i > (int)as.size())
            continue;
        
        LiteralPtr helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        new_clause1 = { make_literal(LiteralType::ORDER, b.id, true, i), helper};
        new_clause2 = { make_literal(LiteralType::ORDER, b.id, false, i-1), helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);

        if(export_proof){
            helper_map[helper->id].push_back({make_literal(LiteralType::ORDER, b.id, true, i)});
            helper_map[helper->id].push_back({make_literal(LiteralType::ORDER, b.id, false, i-1)});

            sat_constraint_clauses.push_back(new_clause1);
            sat_constraint_clauses.push_back(new_clause2);
        }

        auto curr_elem = get_var_from_array(as, i-1);

        new_clause1 = { make_literal(LiteralType::BOOL_VARIABLE, c.id, true, 0),
                        make_literal(LiteralType::BOOL_VARIABLE, curr_elem->id, false, 0),
                         helper};
        new_clause2 = { make_literal(LiteralType::BOOL_VARIABLE, c.id, false, 0),
                        make_literal(LiteralType::BOOL_VARIABLE, curr_elem->id, true, 0),
                        helper};
        cnf_clauses.push_back(new_clause1);
        cnf_clauses.push_back(new_clause2);

        if(export_proof){
            helper_map[helper->id].push_back({make_literal(LiteralType::BOOL_VARIABLE, c.id, true, 0),
                        make_literal(LiteralType::BOOL_VARIABLE, curr_elem->id, false, 0)});
            helper_map[helper->id].push_back({make_literal(LiteralType::BOOL_VARIABLE, c.id, false, 0),
                        make_literal(LiteralType::BOOL_VARIABLE, curr_elem->id, true, 0)});

            sat_constraint_clauses.push_back(new_clause1);
            sat_constraint_clauses.push_back(new_clause2);
        }        

        LiteralPtr not_helper = make_literal(LiteralType::HELPER, helper->id, true, 0);
        helpers.push_back(not_helper);
    }
    
    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }
}

void Encoder::encode_bool2int(const BasicVar& a, const BasicVar& b, CNF& cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *a.name << " " << *b.name << ")\n)\n";
    }

    int b_left = get_left(&b);
    int b_right = get_right(&b);
    
    if(b_left > 1 || b_right < 0){
        declare_unsat(cnf_clauses);
        return;
    }

    if(b_left == 1){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, 1)});

        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0)});
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, 1)});
        }

    }else if(b_right == 0){
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1)});
        
        if(export_proof){
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0)});
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1)});
        }
    } else {

        LiteralPtr yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        LiteralPtr not_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);
        LiteralPtr yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        LiteralPtr not_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, 0),
                                not_helper1});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1),
                                not_helper1});
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0),
                                not_helper1});

        if(export_proof){
            helper_map[not_helper1->id].push_back({make_literal(LiteralType::ORDER, b.id, true, 0)});
            helper_map[not_helper1->id].push_back({make_literal(LiteralType::ORDER, b.id, false, -1)});
            helper_map[not_helper1->id].push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0)});
        
                    sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, 0),
                                not_helper1});
                    sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, -1),
                                            not_helper1});
                    sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0),
                                            not_helper1});
        }
        
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, 1),
                                not_helper2});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, 0),
                                not_helper2});
        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0),
                                not_helper2});
                                
        if(export_proof){
            helper_map[not_helper2->id].push_back({make_literal(LiteralType::ORDER, b.id, true, 1)});
            helper_map[not_helper2->id].push_back({make_literal(LiteralType::ORDER, b.id, false, 0)});
            helper_map[not_helper2->id].push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0)});
            
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, 1),
                                    not_helper2});
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, 0),
                                    not_helper2});
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0),
                                    not_helper2});

        }

        cnf_clauses.push_back({yes_helper1, yes_helper2});

        if(export_proof){
            definition_clauses.push_back({yes_helper1, yes_helper2});
            sat_constraint_clauses.push_back({yes_helper1, yes_helper2});
        }
    }


}


// Encodes a constraint of type a /\ b <=> r
void Encoder::encode_bool_and(const BasicVar& a, const BasicVar& b, const BasicVar& r, CNF &cnf_clauses){
    
    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (= 2 (+ " << *a.name <<  " " <<
                                        *b.name << ")) 1 0))\n)\n";
    }    
    
    LiteralPtr yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, yes_a});
    cnf_clauses.push_back({not_r, yes_b});
    cnf_clauses.push_back({yes_r, not_a, not_b});

    if(export_proof){
        sat_constraint_clauses.push_back({not_r, yes_a});
        sat_constraint_clauses.push_back({not_r, yes_b});
        sat_constraint_clauses.push_back({yes_r, not_a, not_b});
    }

}

// Encodes a constraint of type ⋁i as[i] ∨ ⋁j ¬bs[j]
void Encoder::encode_bool_clause(const ArrayLiteral& as, const ArrayLiteral &bs, CNF& cnf_clauses){
    
    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(<= 1 (+ ";

        for(int i = 0; i < (int)as.size(); i++){
            auto var = get_var_from_array(as, i);
            trivial_encoding_constraints << *var->name << " ";
        }

        for(int i = 0; i < (int)bs.size(); i++){
            auto var = get_var_from_array(bs, i);
            trivial_encoding_constraints << "(- 1 " << *var->name << ") ";
        }

        trivial_encoding_constraints << "))\n)\n";
        
    }


    Clause new_clause;
    
    for(int i = 0; i < (int)as.size(); i++){
        auto var = get_var_from_array(as, i);
        LiteralPtr l = make_literal(LiteralType::BOOL_VARIABLE, var->id, true, 0);
        new_clause.push_back(l);
    }

    for(int j = 0; j < (int)bs.size(); j++){
        auto var = get_var_from_array(bs, j);
        LiteralPtr l = make_literal(LiteralType::BOOL_VARIABLE, var->id, false, 0);
        new_clause.push_back(l);
    }    

    cnf_clauses.push_back(new_clause);

    if(export_proof)
        sat_constraint_clauses.push_back(new_clause);

}

// Encodes constraint of type a = b
void Encoder::encode_bool_eq(const BasicVar &a, const BasicVar& b, CNF &cnf_clauses){
    
    if(export_proof){
        
        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *a.name << " " << *b.name << ")\n)\n";
    }


    LiteralPtr yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);

    cnf_clauses.push_back({yes_a, not_b});
    cnf_clauses.push_back({not_a, yes_b});

    if(export_proof){
        sat_constraint_clauses.push_back({yes_a, not_b});
        sat_constraint_clauses.push_back({not_a, yes_b});
    }

}

// Encodes a constraint of type a = b <=> r
void Encoder::encode_bool_eq_reif(const BasicVar &a, const BasicVar& b, const BasicVar& r, CNF &cnf_clauses){
    
    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (= " << *a.name <<  " " <<
                                        *b.name << ") 1 0))\n)\n";
    }    
    
    LiteralPtr yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({yes_r, not_a, not_b});
    cnf_clauses.push_back({yes_r, yes_a, yes_b});
    cnf_clauses.push_back({not_r, yes_a, not_b});
    cnf_clauses.push_back({not_r, not_a, yes_b});

    if(export_proof){
        sat_constraint_clauses.push_back({yes_r, not_a, not_b});
        sat_constraint_clauses.push_back({yes_r, yes_a, yes_b});
        sat_constraint_clauses.push_back({not_r, yes_a, not_b});
        sat_constraint_clauses.push_back({not_r, not_a, yes_b});
    }
    
}

// Encodes a constraint of type r => a = b
void Encoder::encode_bool_eq_imp(const BasicVar &a, const BasicVar& b, const BasicVar& r, CNF &cnf_clauses){
    
    
    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (= " << *a.name <<  " " <<
                                        *b.name << "))\n)\n";
    }        
    
    LiteralPtr yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, yes_a, not_b});
    cnf_clauses.push_back({not_r, not_a, yes_b});

    if(export_proof){
        sat_constraint_clauses.push_back({not_r, yes_a, not_b});
        sat_constraint_clauses.push_back({not_r, not_a, yes_b});
    }
}

// Encodes constraint of type a <= b
void Encoder::encode_bool_le(const BasicVar &a, const BasicVar& b, CNF &cnf_clauses){

    if(export_proof){
        
        isLIA = true;
    
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(<= " << *a.name << " " << *b.name << ")\n)\n";
    }

    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);

    cnf_clauses.push_back({yes_b, not_a});

    if(export_proof)
        sat_constraint_clauses.push_back({yes_b, not_a});

}

// Encodes a constraint of type a <= b <=> r
void Encoder::encode_bool_le_reif(const BasicVar &a, const BasicVar& b, const BasicVar& r, CNF &cnf_clauses){
    
    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (<= " << *a.name <<  " " <<
                                        *b.name << ") 1 0))\n)\n";
    }    
    
    LiteralPtr yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, not_a, yes_b});
    cnf_clauses.push_back({yes_r, yes_a});
    cnf_clauses.push_back({yes_r, not_b});

    if(export_proof){
        sat_constraint_clauses.push_back({not_r, not_a, yes_b});
        sat_constraint_clauses.push_back({yes_r, yes_a});
        sat_constraint_clauses.push_back({yes_r, not_b});
    }

}

// Encodes a constraint of type r => a <= b
void Encoder::encode_bool_le_imp(const BasicVar &a, const BasicVar& b, const BasicVar& r, CNF &cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (<= " << *a.name <<  " " <<
                                        *b.name << "))\n)\n";
    }   

    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, not_a, yes_b});

    if(export_proof)
        sat_constraint_clauses.push_back({not_r, not_a, yes_b});

}

// Encodes a substitution x = a1*x2 + a2*x2
void Encoder::encode_bool_substitution(const BasicVar &x, const BasicVar &x1, int coef1, const BasicVar &x2, int coef2, CNF& cnf_clauses){

    if(export_proof){

        string coef1_string = coef1 < 0 ? ("(- " + to_string(-coef1) + ")") : to_string(coef1);
        string coef2_string = coef2 < 0 ? ("(- " + to_string(-coef2) + ")") : to_string(coef2);
        
        connection2step << "(= " << *x.name << " (+ (* " << coef1_string << " " << *x1.name << ") (* "
                        << coef2_string << " " << *x2.name << ")))\n";
        connection2step << "---" << endl;
        constraints2step2 << "(= " << *x.name << " (+ (* " << coef1_string << " " << *x1.name << ") (* "
                          << coef2_string << " " << *x2.name << ")))\n";

        smt_step1_funs << "(define-fun f_" << *x.name<< " () Int\n";
        smt_step1_funs << "(+ (* " << coef1_string << " " << *x1.name << ") (* "
                          << coef2_string << " " << *x2.name << "))\n)\n";    
                          
        left_total_step1 << "(= " << *x.name << " f_" << *x.name << ")\n"; 
    }


    int x_left = get_left(&x);
    int x_right = get_right(&x);
    int x1_left = get_left(&x1);
    int x1_right = get_right(&x1);
    int x2_left = get_left(&x2);
    int x2_right = get_right(&x2);

    encode_direct(x, cnf_clauses);
    if(!holds_alternative<BasicParType>(*x1.type))
        encode_direct(x1, cnf_clauses);

    //x = x1 + x2
    Clause helpers;
    for(int i = x_left; i <= x_right; i++){
        for(int j = x1_left; j <= x1_right; j++){
            for(int k = x2_left; k <= x2_right; k++){
                if(j*coef1 + k*coef2 == i){
                    LiteralPtr l_i = make_literal(LiteralType::DIRECT, x.id, true, i);
                    LiteralPtr l_j;
                    if(holds_alternative<BasicParType>(*x1.type))
                        l_j = make_literal(LiteralType::BOOL_VARIABLE, x1.id, j == 0 ? false : true, 0);
                    else    
                        l_j = make_literal(LiteralType::DIRECT, x1.id, true, j);
                    LiteralPtr l_k = make_literal(LiteralType::BOOL_VARIABLE, x2.id, k == 0 ? false : true, 0);

                    LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
                    LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

                    cnf_clauses.push_back({l_i, not_helper});
                    cnf_clauses.push_back({l_j, not_helper});
                    cnf_clauses.push_back({l_k, not_helper});

                    if(export_proof){
                        sat_constraint_clauses.push_back({l_i, not_helper});
                        sat_constraint_clauses.push_back({l_j, not_helper});
                        sat_constraint_clauses.push_back({l_k, not_helper});    
                        
                        helper_map[not_helper->id].push_back({l_i});
                        helper_map[not_helper->id].push_back({l_j});
                        helper_map[not_helper->id].push_back({l_k});
                    }

                    helpers.push_back(yes_helper);
                }   
                
            }
        }
    }    

    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }
}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn = c
void Encoder::encode_bool_lin_eq(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, CNF& cnf_clauses){

    if(export_proof){

        is2step = true;

        constraint2step_set.insert(next_constraint_num);

        constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
        constraints2step1 << "(= (+ ";
        for(int i = 0; i < (int)vars.size(); i++){
            int coef = get_int_from_array(coefs, i);
            string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
            auto var = get_var_from_array(vars, i);
            constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
        }
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
        constraints2step1 << ") "<< c_string << ")\n)\n";
        
        constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";

    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        if(coef > 0){
            sum2 += coef;
        } else {
            sum1 += coef;
        }
    }
    if(c < sum1 || c > sum2){
        if(export_proof && is2step)
            constraints2step2 << "false\n)\n";

        declare_unsat(cnf_clauses);
        return ;
    }    

    if(vars.size() == 1){

        auto var = get_var_from_array(vars, 0);
        int coef = get_int_from_array(coefs, 0);
        if(c == 0){
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, var->id, false, 0)}); 
            if(export_proof){
                if(is2step)
                    constraints2step2 << "(= " << *var->name << " 0)\n)\n";
                sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, var->id, false, 0)});
            }
        } else if(c == coef) {
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, var->id, true, 0)});
            if(export_proof){
                sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, var->id, true, 0)});
                if(is2step)
                    constraints2step2 << "(= " << *var->name << " 1)\n)\n";
            }
        } else {
            if(is2step)
                constraints2step2 << "false\n)\n";
            declare_unsat(cnf_clauses);
        }
        return;
    }

    if(export_proof)
        constraints2step2 << "(and\n";

    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    int lower_bound1 = min({coef0, 0});
    int upper_bound1 = max({coef0, 0}); 
    int lower_bound2 = min({coef1, 0});
    int upper_bound2 = max({coef1, 0}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
    encode_bool_substitution(*var, *get_var_from_array(vars, 0), get_int_from_array(coefs, 0),
                        *get_var_from_array(vars, 1), get_int_from_array(coefs, 1), cnf_clauses);
    
    BasicVar* var1;
    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(var);
        upper_bound1 = get_right(var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = get_var_from_array(vars, i);
        lower_bound2 = min({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        upper_bound2 = max({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);

        encode_bool_substitution(*var1, *var, 1, *get_var_from_array(vars, i), get_int_from_array(coefs, i), cnf_clauses);

        var = var1;
    }

    if(vars.size() == 2){
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c - 1)});
        
        if(export_proof){            
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step2 << "(= " << *var->name << " " << c_string << ")\n";

            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c)});
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, false, c - 1)});
        }   
    } else {
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c)});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, false, c - 1)});

        if(export_proof){            
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step2 << "(= " << *var1->name << " " << c_string << ")\n";

            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c)});
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, false, c - 1)});
        }   
    }

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }

}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn <= c
void Encoder::encode_bool_lin_le(const ArrayLiteral& coefs, const ArrayLiteral &vars, int c, CNF& cnf_clauses){

    if(export_proof){

        is2step = true;

        constraint2step_set.insert(next_constraint_num);

        constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
        constraints2step1 << "(<= (+ ";
        for(int i = 0; i < (int)vars.size(); i++){
            int coef = get_int_from_array(coefs, i);
            string coef_string = coef < 0 ? ("(- " + to_string(-coef) + ")") : to_string(coef);
            auto var = get_var_from_array(vars, i);
            constraints2step1 << "(* " << coef_string << " " << *var->name << ") ";
        }
        string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
        constraints2step1 << ") "<< c_string << ")\n)\n";
        
        constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";

    }

    int sum1 = 0, sum2 = 0;
    for(int i = 0; i < (int)coefs.size(); i++){
        auto coef = get_int_from_array(coefs, i);
        if(coef > 0){
            sum2 += coef;
        } else {
            sum1 += coef;
        }
    }

    if(c < sum1){
        if(export_proof && is2step)
            constraints2step2 << "false\n)\n";

        declare_unsat(cnf_clauses);
        return ;
    }
    if(c > sum2){
        if(export_proof){
            if(is2step)
                constraints2step2 << "true\n)\n";
            
            auto var = get_var_from_array(vars, 0);
            LiteralPtr yes_var = make_literal(LiteralType::BOOL_VARIABLE, var->id, true, 0); 
            LiteralPtr not_var = make_literal(LiteralType::BOOL_VARIABLE, var->id, false, 0); 
            sat_constraint_clauses.push_back({yes_var, not_var});

        }
        return ;
    }           

    if(vars.size() == 1){

        auto var = get_var_from_array(vars, 0);
        int coef = get_int_from_array(coefs, 0);
        if(c < coef){
            cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, var->id, false, 0)}); 
            if(export_proof){
                sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, var->id, false, 0)});
                if(is2step)
                    constraints2step2 << "(= " << *var->name << " 0)\n)\n";
            }
        } else {
            if(is2step)
                constraints2step2 << "true\n)\n";
        }
        return;
    }

    if(export_proof)
        constraints2step2 << "(and\n";

    auto coef0 = get_int_from_array(coefs, 0);
    auto coef1 = get_int_from_array(coefs, 1);

    int lower_bound1 = min({coef0, 0});
    int upper_bound1 = max({coef0, 0}); 
    int lower_bound2 = min({coef1, 0});
    int upper_bound2 = max({coef1, 0}); 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);
    encode_bool_substitution(*var, *get_var_from_array(vars, 0), get_int_from_array(coefs, 0),
                        *get_var_from_array(vars, 1), get_int_from_array(coefs, 1), cnf_clauses);
    
    BasicVar* var1;
    for(int i = 2; i < (int)coefs.size(); i++){
 
        lower_bound1 = get_left(var);
        upper_bound1 = get_right(var);
        auto coef_i = get_int_from_array(coefs, i);
        auto var_i = get_var_from_array(vars, i);
        lower_bound2 = min({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        upper_bound2 = max({get_left(var_i)*coef_i, get_right(var_i)*coef_i});
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses, true);

        encode_bool_substitution(*var1, *var, 1, *get_var_from_array(vars, i), get_int_from_array(coefs, i), cnf_clauses);

        var = var1;
    }

    if(vars.size() == 2){
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c)});
        
        if(export_proof){            
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step2 << "(<= " << *var->name << " " << c_string << ")\n";

            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var->id, true, c)});
        }   
    } else {
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c)});

        if(export_proof){            
            string c_string = c < 0 ? ("(- " + to_string(-c) + ")") : to_string(c);
            constraints2step2 << "(<= " << *var1->name << " " << c_string << ")\n";

            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, var1->id, true, c)});
        }   
    }

    if(export_proof){
        constraints2step2 << ")\n)\n";
    }

}

// Encodes constraint of type a < b
void Encoder::encode_bool_lt(const BasicVar &a, const BasicVar& b, CNF &cnf_clauses){
    
    if(export_proof){
        
        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(< " << *a.name << " " << *b.name << ")\n)\n";
    }    
    
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);

    cnf_clauses.push_back({yes_b});
    cnf_clauses.push_back({not_a});
    cnf_clauses.push_back({yes_b, not_a});

    if(export_proof){
        sat_constraint_clauses.push_back({yes_b});
        sat_constraint_clauses.push_back({not_a});
        sat_constraint_clauses.push_back({yes_b, not_a});
    }

}

// Encodes a constraint of type a < b <=> r
void Encoder::encode_bool_lt_reif(const BasicVar &a, const BasicVar& b, const BasicVar& r, CNF &cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (< " << *a.name <<  " " <<
                                        *b.name << ") 1 0))\n)\n";
    }

    LiteralPtr yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({yes_r, yes_a, not_b});
    cnf_clauses.push_back({not_r, not_a});
    cnf_clauses.push_back({not_r, yes_b});

    if(export_proof){
        sat_constraint_clauses.push_back({yes_r, yes_a, not_b});
        sat_constraint_clauses.push_back({not_r, not_a});
        sat_constraint_clauses.push_back({not_r, yes_b});
    }
}

// Encodes a constraint of type r => a < b
void Encoder::encode_bool_lt_imp(const BasicVar &a, const BasicVar& b, const BasicVar& r, CNF &cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (< " << *a.name <<  " " <<
                                        *b.name << "))\n)\n";
    }

    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, not_a});
    cnf_clauses.push_back({not_r, yes_b});

    if(export_proof){
        sat_constraint_clauses.push_back({not_r, not_a});
        sat_constraint_clauses.push_back({not_r, yes_b});   
    }
}

// Encodes constraint of type a =/= b
void Encoder::encode_bool_not(const BasicVar &a, const BasicVar& b, CNF &cnf_clauses){

    if(export_proof){
        
        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(distinct " << *a.name << " " << *b.name << ")\n)\n";
    }

    LiteralPtr yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);

    cnf_clauses.push_back({not_a, not_b});
    cnf_clauses.push_back({yes_a, yes_b});

    if(export_proof){
        sat_constraint_clauses.push_back({not_a, not_b});
        sat_constraint_clauses.push_back({yes_a, yes_b});
    }

}

// Encodes a constraint of type a \/ b <=> r
void Encoder::encode_bool_or(const BasicVar &a, const BasicVar& b, const BasicVar& r, CNF &cnf_clauses){
    
    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (>= (+ " << *a.name <<  " " <<
                                        *b.name << ") 1) 1 0))\n)\n";
    }    
    
    LiteralPtr yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({yes_r, not_a});
    cnf_clauses.push_back({yes_r, not_b});
    cnf_clauses.push_back({not_r, yes_a, yes_b});

    if(export_proof){
        sat_constraint_clauses.push_back({yes_r, not_a});
        sat_constraint_clauses.push_back({yes_r, not_b});
        sat_constraint_clauses.push_back({not_r, yes_a, yes_b});
    }

}

// Encodes a constraint of type a xor b <=> r
void Encoder::encode_bool_xor(const BasicVar &a, const BasicVar& b, const BasicVar& r, CNF &cnf_clauses){
    
    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (distinct " << *a.name <<  " " <<
                                        *b.name << ") 1 0))\n)\n";
    }
    
    LiteralPtr yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({not_r, yes_a, yes_b});
    cnf_clauses.push_back({not_r, not_a, not_b});
    cnf_clauses.push_back({yes_r, not_a, yes_b});
    cnf_clauses.push_back({yes_r, yes_a, not_b});

    if(export_proof){
        sat_constraint_clauses.push_back({not_r, yes_a, yes_b});
        sat_constraint_clauses.push_back({not_r, not_a, not_b});
        sat_constraint_clauses.push_back({yes_r, not_a, yes_b});
        sat_constraint_clauses.push_back({yes_r, yes_a, not_b});
    }
}

// Encodes a constraint of type a xor b <=> true
void Encoder::encode_bool_xor(const BasicVar &a, const BasicVar& b, CNF &cnf_clauses){
    
    if(export_proof){
        
        isLIA = true;
     
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(distinct " << *a.name << " " << *b.name << ")\n)\n";
    }

    LiteralPtr yes_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, true, 0);
    LiteralPtr yes_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, true, 0);
    LiteralPtr not_a = make_literal(LiteralType::BOOL_VARIABLE, a.id, false, 0);
    LiteralPtr not_b = make_literal(LiteralType::BOOL_VARIABLE, b.id, false, 0);

    cnf_clauses.push_back({yes_a, yes_b});
    cnf_clauses.push_back({not_a, not_b});

    if(export_proof){
        sat_constraint_clauses.push_back({yes_a, yes_b});
        sat_constraint_clauses.push_back({not_a, not_b});
    }

}

// ---------------------------- Encoding Set constraints -------------------------------------

bool Encoder::check_if_val_in_domain(const vector<int>& elems, int val){
    return binary_search(elems.begin(), elems.end(), val);
}

// Encodes a constraint of type as[b] = c
void Encoder::encode_array_set_element(const BasicVar& b, const ArrayLiteral& as, const BasicVar& c, CNF& cnf_clauses){

    if(export_proof){
        isLIA = true;
        isUF = true;


        string arr_name = "arr_" + to_string(next_array++);
        trivial_encoding_vars << "(declare-fun " << arr_name << " (Int) (_ BitVec \n"; 

        for(int i = 0; i < (int)as.size(); i++){
            auto var = get_var_from_array(as, i);
            trivial_encoding_domains << "(= " << *var->name << " (" << arr_name << " "
                               << i+1 << "))\n";
            right_total << "(= " << *var->name << " (" << arr_name << " "
                               << i+1 << "))\n";
        }

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(and\n";
        trivial_encoding_constraints << "(<= 1 " << *b.name << " " << as.size() << ")\n";

        trivial_encoding_constraints << "(= " << *c.name << " (" << arr_name << " " << *b.name << "))\n)\n)\n";
        
    }

    int b_left = get_left(&b);
    int b_right = get_right(&b);

    Clause helpers;
    for(int i = b_left; i <= b_right; i++){
        if(i < 1 || i > (int)as.size())
            continue;

        LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        auto curr_var = *get_set_from_array(as, i-1);

        vector<int> elems;
        if(holds_alternative<SetSetLiteral*>(curr_var)){
            elems = *get<SetSetLiteral*>(curr_var)->elems;
        } else {
            int left = get<SetRangeLiteral*>(curr_var)->left;
            int right = get<SetRangeLiteral*>(curr_var)->right;
            for(int i = left; i <= right; i++)
                elems.push_back(i);
        }

        CNF temp_clauses;
        int j = 0, k = 0;
        auto cs = *get_set_elems(c);
    
        
        while(j < (int)elems.size() && k < (int)cs.size()){
            if(elems[j] < cs[k]){
                temp_clauses.push_back({not_helper});
                j++;
            } else if(elems[j] > cs[k]){
                temp_clauses.push_back({make_literal(LiteralType::SET_ELEM, c.id, false, cs[k])});
                k++;
            } else {
                LiteralPtr yes_c = make_literal(LiteralType::SET_ELEM, c.id, true, cs[k]);
            
                temp_clauses.push_back({yes_c});
                j++; k++;
            }
        }
    
        if(j < (int)elems.size()){
            temp_clauses.push_back({not_helper});
        }

        while(k < (int)cs.size())
            temp_clauses.push_back({make_literal(LiteralType::SET_ELEM, c.id, false, cs[k++])});
        
        for(auto clause : temp_clauses){

            if(clause[0] == not_helper){
                cnf_clauses.push_back(clause);

                if(export_proof)
                    sat_constraint_clauses.push_back(clause);
                continue;
            }
                

            if(export_proof)
                helper_map[not_helper->id].push_back(clause);

            clause.push_back(not_helper);
            cnf_clauses.push_back(clause);

            if(export_proof)
                sat_constraint_clauses.push_back(clause);
        }

        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, i), not_helper});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, i - 1), not_helper});

        if(export_proof){
            helper_map[not_helper->id].push_back({make_literal(LiteralType::ORDER, b.id, true, i)});
            helper_map[not_helper->id].push_back({make_literal(LiteralType::ORDER, b.id, false, i - 1)});

            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, i), not_helper});
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, i - 1), not_helper});
        }

        helpers.push_back(yes_helper);
    }

    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }
}

// Encodes a constraint of type as[b] = c
void Encoder::encode_array_var_set_element(const BasicVar& b, const ArrayLiteral& as, const BasicVar& c, CNF& cnf_clauses){

    if(export_proof){

        isLIA = true;

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(and\n";
        trivial_encoding_constraints << "(<= 1 " << *b.name << " " << as.size() << ")\n";
        trivial_encoding_constraints << "(= " << *c.name << "\n";
        for(int i = 0; i < (int)as.size(); i++){
            auto var = get_var_from_array(as, i);
            trivial_encoding_constraints << "(ite (= " << *b.name << " " << i + 1 << ") " << *var->name << "\n";
        }

        trivial_encoding_constraints << "(bvneg " << *c.name << ")" << endl;
        for(int i = 0; i < (int)as.size() + 2; i++)
            trivial_encoding_constraints << ")";
        
        trivial_encoding_constraints << ")\n";
    }

    int b_left = get_left(&b);
    int b_right = get_right(&b);

    Clause helpers;
    for(int i = b_left; i <= b_right; i++){
        if(i < 1 || i > (int)as.size())
            continue;

        LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        auto curr_var = *get_var_from_array(as, i-1);

        CNF temp_clauses;
        if(export_proof){
            export_proof = false;
            encode_set_eq(curr_var, c, temp_clauses);
            export_proof = true;
        } else
            encode_set_eq(curr_var, c, temp_clauses);
        
        for(auto clause : temp_clauses){
            if(export_proof)
                helper_map[not_helper->id].push_back(clause);

            clause.push_back(not_helper);
            cnf_clauses.push_back(clause);

            if(export_proof)
                sat_constraint_clauses.push_back(clause);
        }

        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, i), not_helper});
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, i - 1), not_helper});

        if(export_proof){
            helper_map[not_helper->id].push_back({make_literal(LiteralType::ORDER, b.id, true, i)});
            helper_map[not_helper->id].push_back({make_literal(LiteralType::ORDER, b.id, false, i - 1)});

            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, true, i), not_helper});
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, b.id, false, i - 1), not_helper});            
        }

        helpers.push_back(yes_helper);
    }

    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }
}

// Encodes a substitution x = a1*x2 + a2*x2
void Encoder::encode_set_substitution(const BasicVar &x, const BasicVar &x1, int val1, int val2, const BasicVar& S, CNF& cnf_clauses){

    if(export_proof){
        if(x1.id == x.id){
            connection2step << "(= " << *x.name << " (+ (bv2nat ((_ extract " << val1 - bv_left << " " 
                            << val1 - bv_left << ") " << *S.name << ")) (bv2nat ((_ extract "
                            << val2 - bv_left << " " << val2 - bv_left << ") " << *S.name << "))))\n";
            connection2step << "---" << endl;
                        
            constraints2step2 << "(= " << *x.name << " (+ (bv2nat ((_ extract " << val1 - bv_left << " " 
                            << val1 - bv_left << ") " << *S.name << ")) (bv2nat ((_ extract "
                            << val2 - bv_left << " " << val2 - bv_left << ") " << *S.name << "))))\n";
    
            smt_step1_funs << "(define-fun f_" << *x.name<< " () Int\n";
            smt_step1_funs << " (+ (bv2nat ((_ extract " << val1 - bv_left << " " 
                            << val1 - bv_left << ") " << *S.name << ")) (bv2nat ((_ extract "
                            << val2 - bv_left << " " << val2 - bv_left << ") " << *S.name << ")))\n)\n";
      
                            
            left_total_step1 << "(= " << *x.name << " f_" << *x.name << ")\n"; 
        } else {
            connection2step << "(= " << *x.name << " (+ " << *x1.name << " (bv2nat ((_ extract "
                            << val2 - bv_left << " " << val2 - bv_left << ") " << *S.name << "))))\n";
            connection2step << "---" << endl;
                        
            constraints2step2 << "(= " << *x.name << " (+ " << *x1.name << " (bv2nat ((_ extract "
                            << val2 - bv_left << " " << val2 - bv_left << ") " << *S.name << "))))\n";
    
            smt_step1_funs << "(define-fun f_" << *x.name<< " () Int\n";
            smt_step1_funs << "(+ " << *x1.name << " (bv2nat ((_ extract "
                            << val2 - bv_left << " " << val2 - bv_left << ") " << *S.name << ")))\n)\n";
     
                            
            left_total_step1 << "(= " << *x.name << " f_" << *x.name << ")\n"; 
        }
    }

    int x_left = get_left(&x);
    int x_right = get_right(&x);
    int x1_left = get_left(&x1);
    int x1_right = get_right(&x1);
    if(x1.id == x.id){
        x1_left = 0;
        x1_right = 1;
    }

    encode_direct(x, cnf_clauses);
    if(x1.id != x.id)
        encode_direct(x1, cnf_clauses);

    //x = x1 + x2
    Clause helpers;
    for(int i = x_left; i <= x_right; i++){
        for(int j = x1_left; j <= x1_right; j++){
            for(int k = 0; k <= 1; k++){
                if(j + k == i){
                    LiteralPtr l_i = make_literal(LiteralType::DIRECT, x.id, true, i);
                    LiteralPtr l_j;
                    if(x.id == x1.id)
                        l_j = make_literal(LiteralType::SET_ELEM, S.id, j == 0 ? false : true, val1);
                    else    
                        l_j = make_literal(LiteralType::DIRECT, x1.id, true, j);
                    LiteralPtr l_k = make_literal(LiteralType::SET_ELEM, S.id, k == 0 ? false : true, val2);

                    LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
                    LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

                    cnf_clauses.push_back({l_i, not_helper});
                    cnf_clauses.push_back({l_j, not_helper});
                    cnf_clauses.push_back({l_k, not_helper});

                    if(export_proof){
                        helper_map[not_helper->id].push_back({l_i});
                        helper_map[not_helper->id].push_back({l_j});
                        helper_map[not_helper->id].push_back({l_k});

                        sat_constraint_clauses.push_back({l_i, not_helper});
                        sat_constraint_clauses.push_back({l_j, not_helper});       
                        sat_constraint_clauses.push_back({l_k, not_helper});       
                    }

                    helpers.push_back(yes_helper);
                }   
                
            }
        }
    }    

    cnf_clauses.push_back(helpers);
    if(export_proof){
        sat_constraint_clauses.push_back(helpers);
        definition_clauses.push_back(helpers);
    }

}

// Encodes a constraint of type |S| = x
void Encoder::encode_set_card(const BasicVar& S, const BasicVar& x, CNF& cnf_clauses){

    auto elems = *get_set_elems(S);
    int left = get_left(&x);
    int right = get_right(&x);

    if(export_proof){
        needOnes = true;

        if(elems.size() > 1){
            is2step = true;

            constraint2step_set.insert(next_constraint_num);

            constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
            constraints2step1 << "(= " << *x.name << " (ones " << *S.name << "))\n)\n";

            constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            constraints2step2 << "(and\n";
        } else {

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= " << *x.name << " (ones " << *S.name << "))\n)\n";            
        }
    }

    if(left > (int)elems.size() || right < 0){

        if(is2step)
            constraints2step2 << "false)\n)\n"; 
        declare_unsat(cnf_clauses);
        return;
    }

    //TODO
    if(elems.size() == 1){

        if(right == 0){
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, -1)});
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, false, elems[0])});

            if(export_proof){
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, -1)});
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, false, elems[0])});
            }
        } else if(left == 1){
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, 1)});
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, true, elems[0])});

            if(export_proof){
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, 1)});
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, true, elems[0])});
            }

        } else {

            LiteralPtr not_helper1 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
            LiteralPtr yes_helper1 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, -1), not_helper1});
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, 0), not_helper1});
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, false, elems[0]), not_helper1});

            if(export_proof){
                helper_map[not_helper1->id].push_back({make_literal(LiteralType::ORDER, x.id, false, -1)});
                helper_map[not_helper1->id].push_back({make_literal(LiteralType::ORDER, x.id, true, 0)});
                helper_map[not_helper1->id].push_back({make_literal(LiteralType::SET_ELEM, S.id, false, elems[0])});

                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, -1), not_helper1});
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, 0), not_helper1});
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, false, elems[0]), not_helper1});

            }

            LiteralPtr not_helper2 = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
            LiteralPtr yes_helper2 = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);

            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, 0), not_helper2});
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, 1), not_helper2});
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, true, elems[0]), not_helper2});

            if(export_proof){
                helper_map[not_helper2->id].push_back({make_literal(LiteralType::ORDER, x.id, false, 0)});
                helper_map[not_helper2->id].push_back({make_literal(LiteralType::ORDER, x.id, true, 1)});
                helper_map[not_helper2->id].push_back({make_literal(LiteralType::SET_ELEM, S.id, true, elems[0])});

                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, 0), not_helper2});
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, 1), not_helper2});
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, true, elems[0]), not_helper2});

                sat_constraint_clauses.push_back({yes_helper1, yes_helper2});
                definition_clauses.push_back({yes_helper1, yes_helper2});
            }

            cnf_clauses.push_back({yes_helper1, yes_helper2});

        }
        return;
    }

    int lower_bound = 0;
    int upper_bound = 2;

    BasicVar* var = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_set_substitution(*var, *var, elems[0], elems[1], S, cnf_clauses);
    
    BasicVar* var1;
    for(int i = 2; i < (int)elems.size(); i++){
 
        lower_bound = 0;
        upper_bound = i + 1;


        var1 = encode_int_range_helper_variable(lower_bound, upper_bound, cnf_clauses);

        encode_set_substitution(*var1, *var, 1, elems[i], S, cnf_clauses);

        var = var1;
    }

    CNF temp_clauses;
    if(export_proof){
        export_proof = false;
        
        if(elems.size() == 2){
            encode_int_eq(x, *var, temp_clauses);

            constraints2step2 << "(= " << *x.name << " " << *var->name << ")\n)\n)\n";
        } else {
            encode_int_eq(x, *var1, temp_clauses);

            constraints2step2 << "(= " << *x.name << " " << *var1->name << ")\n)\n)\n";
        }

        for(auto clause : temp_clauses)
            sat_constraint_clauses.push_back(clause);

        export_proof = true;

        
    } else {
        
        if(elems.size() == 2){
            encode_int_eq(x, *var, cnf_clauses);
        } else {
            encode_int_eq(x, *var1, cnf_clauses);
        }

    }
}

// Encodes a constraint of type r = x \ y
void Encoder::encode_set_diff(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){

    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (bvand " << *x.name << " (bvnot " << *y.name << ")))\n)\n";
    }

    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    auto rs = *get_set_elems(r);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){

            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            if(!check_if_val_in_domain(rs, xs[i])){
                cnf_clauses.push_back({not_x});

                if(export_proof)
                    sat_constraint_clauses.push_back({not_x});
            } else {

                cnf_clauses.push_back({yes_x, not_r});
                cnf_clauses.push_back({not_x, yes_r});    
                
                if(export_proof){
                    sat_constraint_clauses.push_back({yes_x, not_r});
                    sat_constraint_clauses.push_back({not_x, yes_r}); 
                }
            }
            i++;
        } else if(xs[i] > ys[j]){
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);

            if(check_if_val_in_domain(rs, ys[j])){
                cnf_clauses.push_back({not_r});    
                
                if(export_proof)
                    sat_constraint_clauses.push_back({not_r});
            }
            j++;
        } else {
            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, xs[i]);
            LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, xs[i]);
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            if(!check_if_val_in_domain(rs, xs[i])){
                cnf_clauses.push_back({not_x, yes_y});

                if(export_proof){
                    sat_constraint_clauses.push_back({not_x, yes_y});
                }
            } else {

                cnf_clauses.push_back({not_r, yes_x});
                cnf_clauses.push_back({not_r, not_y});
                cnf_clauses.push_back({yes_r, not_x, yes_y}); 

                if(export_proof){
                    sat_constraint_clauses.push_back({not_r, yes_x});
                    sat_constraint_clauses.push_back({not_r, not_y});
                    sat_constraint_clauses.push_back({yes_r, not_x, yes_y});             
                }
            }

            i++; j++;
        }
    }

    while(i < (int)xs.size()){
        LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
        LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
        LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
        LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);

        if(!check_if_val_in_domain(rs, xs[i])){
            cnf_clauses.push_back({not_x});

            if(export_proof)
                sat_constraint_clauses.push_back({not_x});
        } else {

            cnf_clauses.push_back({yes_x, not_r});
            cnf_clauses.push_back({not_x, yes_r});   
            
            if(export_proof){
                sat_constraint_clauses.push_back({yes_x, not_r});
                sat_constraint_clauses.push_back({not_x, yes_r});              
            }
        }
        
        i++;
    }

    for(int i = 0; i < (int)rs.size(); i++){
        if(!binary_search(xs.begin(), xs.end(), rs[i])){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, r.id, false, rs[i])});

            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, r.id, false, rs[i])});
        }
    }

}

// Encodes a constraint of type x = y
void Encoder::encode_set_eq(const BasicVar& x, const BasicVar& y, CNF &cnf_clauses){

    if(export_proof){

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *x.name << " " << *y.name << ")\n)\n";
    }

    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i])});

            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i])});

            i++;
        } else if(xs[i] > ys[j]){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, y.id, false, ys[j])});

            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, y.id, false, ys[j])});

            j++;
        } else {
            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);
        
            cnf_clauses.push_back({yes_x, not_y});
            cnf_clauses.push_back({not_x, yes_y});    
            
            if(export_proof){
                sat_constraint_clauses.push_back({yes_x, not_y});
                sat_constraint_clauses.push_back({not_x, yes_y});
            }

            i++; j++;
        }
    }

    while(i < (int)xs.size()){
        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i])});
        if(export_proof)
            sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i])});
        i++;
    }

    while(j < (int)ys.size()){
        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, y.id, false, ys[j])});
        if(export_proof)
            sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, y.id, false, ys[j])});
        j++;
    }
}

// Encodes a constraint of type (x = y) <=> r
void Encoder::encode_set_eq_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){

    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (= " 
                                     << *x.name << " " << *y.name << ") 1 0))\n)\n";
    }

    CNF temp_clauses;
    if(export_proof){
        export_proof = false;
        encode_set_eq(x, y, temp_clauses);
        export_proof = true;
    } else
        encode_set_eq(x, y, temp_clauses);

    reify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type r => (x = y)
void Encoder::encode_set_eq_imp(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){

    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (= " 
                                     << *x.name << " " << *y.name << "))\n)\n";
    }

    CNF temp_clauses;
    if(export_proof){
        export_proof = false;
        encode_set_eq(x, y, temp_clauses);
        export_proof = true;
    } else
        encode_set_eq(x, y, temp_clauses);

    impify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type x ∈ y
void Encoder::encode_set_in(const BasicVar& x, const BasicVar& S, CNF &cnf_clauses){
    
    auto elems = *get_set_elems(S);
    auto left = get_left(&x);
    auto right = get_right(&x);

    if(left > elems[elems.size() - 1] || right < elems[0]){
        declare_unsat(cnf_clauses);
        return ;
    }

    Clause helpers;
    for(auto elem : elems){
        LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        if(elem >= left && elem <= right){
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, elem),
                                    not_helper});
            cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, elem-1),
                                    not_helper});
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, true, elem),
                                    not_helper});

            if(export_proof){
                helper_map[not_helper->id].push_back({make_literal(LiteralType::ORDER, x.id, true, elem)});
                helper_map[not_helper->id].push_back({make_literal(LiteralType::ORDER, x.id, false, elem-1)});
                helper_map[not_helper->id].push_back({make_literal(LiteralType::SET_ELEM, S.id, true, elem)});

                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, elem),
                                    not_helper});
                sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, false, elem-1),
                                    not_helper});
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, S.id, true, elem),
                                    not_helper});
            }

            helpers.push_back(yes_helper);

        }
    }

    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }
    if(export_proof){
        set_in_pairs.push_back({*x.name, *S.name});
    }
}

// Encodes a constraint of type (x ∈ S) <=> r, where S is a set parameter
void Encoder::encode_set_in_reif(const BasicVar& x, const BasicLiteralExpr& S1, const BasicVar& r, CNF &cnf_clauses){
    
    auto S = get<SetLiteral*>(S1);
    auto left = get_left(&x);
    auto right = get_right(&x);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

    vector<int> elems;
    if(holds_alternative<SetSetLiteral*>(*S)){
        elems = *get<SetSetLiteral*>(*S)->elems;
    } else {
        int left = get<SetRangeLiteral*>(*S)->left;
        int right = get<SetRangeLiteral*>(*S)->right;
        for(int i = left; i <= right; i++)
            elems.push_back(i);
    }

    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite ";
        if(elems.size() > 1)
            trivial_encoding_constraints << "(or ";
        for(auto elem : elems){
            trivial_encoding_constraints << "(= " << *x.name << " " << elem << ") ";
        }
        if(elems.size() > 1)
            trivial_encoding_constraints << ")";
        trivial_encoding_constraints << " 1 0))\n)\n";
    }

    if(left > elems[elems.size() - 1] || right < elems[0]){
        cnf_clauses.push_back({not_r});

        if(export_proof)
            sat_constraint_clauses.push_back({not_r});
    } else {

        Clause helpers;
        for(auto elem : elems){
            LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
            LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
            if(elem >= left && elem <= right){    
                
                Clause new_clause1;

                LiteralPtr not_p1 = make_literal(LiteralType::ORDER, x.id, false, elem);
                LiteralPtr yes_p1 = make_literal(LiteralType::ORDER, x.id, true, elem); 
                LiteralPtr not_p2 = make_literal(LiteralType::ORDER, x.id, true, elem-1);
                LiteralPtr yes_p2 = make_literal(LiteralType::ORDER, x.id, false, elem-1); 
                
                new_clause1.push_back(not_p1);
                new_clause1.push_back(not_p2);

                Clause new_clause2 = {yes_p1, not_helper};
                cnf_clauses.push_back(new_clause2);

                if(export_proof){
                    helper_map[not_helper->id].push_back({yes_p1});

                    sat_constraint_clauses.push_back(new_clause2);
                }

                new_clause2 = {yes_p2, not_helper};
                cnf_clauses.push_back(new_clause2);

                if(export_proof){
                    helper_map[not_helper->id].push_back({yes_p2});

                    sat_constraint_clauses.push_back(new_clause2);
                }

                if(export_proof){
                    helper_map[-yes_helper->id].push_back(new_clause1);
                }

                new_clause1.push_back(yes_helper);
                cnf_clauses.push_back(new_clause1);

                if(export_proof){
                    sat_constraint_clauses.push_back(new_clause1);
                }

                helpers.push_back(yes_helper);
            }
        }

        CNF temp_clauses = {helpers};
        reify(temp_clauses, r, cnf_clauses);
    }

}

// Encodes a constraint of type (x ∈ S) <=> r, where S is a set variable
void Encoder::encode_set_in_reif(const BasicVar& x, const BasicVar& S, const BasicVar& r, CNF &cnf_clauses){
    
    auto elems = *get_set_elems(S);
    auto left = get_left(&x);
    auto right = get_right(&x);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

    if(left > elems[elems.size() - 1] || right < elems[0]){
        cnf_clauses.push_back({not_r});

        if(export_proof){
            sat_constraint_clauses.push_back({not_r});

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= " << *r.name << " 0)\n)\n";
        }
        return ;
    }

    Clause helpers;
    for(auto elem : elems){
        LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        if(elem >= left && elem <= right){    
            Clause new_clause1;

            LiteralPtr not_p1 = make_literal(LiteralType::ORDER, x.id, false, elem);
            LiteralPtr yes_p1 = make_literal(LiteralType::ORDER, x.id, true, elem); 
            LiteralPtr not_p2 = make_literal(LiteralType::ORDER, x.id, true, elem-1);
            LiteralPtr yes_p2 = make_literal(LiteralType::ORDER, x.id, false, elem-1); 
            LiteralPtr not_p3 = make_literal(LiteralType::SET_ELEM, S.id, false, elem);
            LiteralPtr yes_p3 = make_literal(LiteralType::SET_ELEM, S.id, true, elem); 
                
            new_clause1.push_back(not_p1);
            new_clause1.push_back(not_p2);
            new_clause1.push_back(not_p3);
        
            Clause new_clause2 = {yes_p1, not_helper};
            cnf_clauses.push_back(new_clause2);

            if(export_proof){
                helper_map[not_helper->id].push_back({yes_p1});

                sat_constraint_clauses.push_back(new_clause2);
            }

            new_clause2 = {yes_p2, not_helper};
            cnf_clauses.push_back(new_clause2);
            
            if(export_proof){
                helper_map[not_helper->id].push_back({yes_p2});

                sat_constraint_clauses.push_back(new_clause2);
            }

            new_clause2 = {yes_p3, not_helper};
            cnf_clauses.push_back(new_clause2);
        
            if(export_proof){
                helper_map[not_helper->id].push_back({yes_p3});

                sat_constraint_clauses.push_back(new_clause2);
            }

            new_clause1.push_back(yes_helper);
            cnf_clauses.push_back(new_clause1);
            
            if(export_proof){
                helper_map[-yes_helper->id].push_back({not_p1, not_p2, not_p3});

                sat_constraint_clauses.push_back(new_clause1);
            }

            helpers.push_back(yes_helper);
        }
    }

    CNF temp_clauses = {helpers};

    reify(temp_clauses, r, cnf_clauses);

    if(export_proof){
        set_in_reif_pairs.push_back({*x.name, *S.name, *r.name});
    }

}

// Encodes a constraint of type (x ∈ S) => r, where S is a set parameter
void Encoder::encode_set_in_imp(const BasicVar& x, const BasicLiteralExpr& S1, const BasicVar& r, CNF &cnf_clauses){
    
    
    auto S = get<SetLiteral*>(S1);
    auto left = get_left(&x);
    auto right = get_right(&x);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

    vector<int> elems;
    if(holds_alternative<SetSetLiteral*>(*S)){
        elems = *get<SetSetLiteral*>(*S)->elems;
    } else {
        int left = get<SetRangeLiteral*>(*S)->left;
        int right = get<SetRangeLiteral*>(*S)->right;
        for(int i = left; i <= right; i++)
            elems.push_back(i);
    }

    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) ";
        if(elems.size() > 1)
            trivial_encoding_constraints << "(or ";
        for(auto elem : elems){
            trivial_encoding_constraints << "(= " << *x.name << " " << elem << ") ";
        }
        if(elems.size() > 1)
            trivial_encoding_constraints << ")";
        trivial_encoding_constraints << ")\n)\n";
    }

    if(left > elems[elems.size() - 1] || right < elems[0]){
        cnf_clauses.push_back({not_r});

        if(export_proof)
            sat_constraint_clauses.push_back({not_r});
    } else {

        Clause helpers;
        for(auto elem : elems){
            LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
            LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
            if(elem >= left && elem <= right){    
                
                Clause new_clause1;

                LiteralPtr not_p1 = make_literal(LiteralType::ORDER, x.id, false, elem);
                LiteralPtr yes_p1 = make_literal(LiteralType::ORDER, x.id, true, elem); 
                LiteralPtr not_p2 = make_literal(LiteralType::ORDER, x.id, true, elem-1);
                LiteralPtr yes_p2 = make_literal(LiteralType::ORDER, x.id, false, elem-1); 
                
                new_clause1.push_back(not_p1);
                new_clause1.push_back(not_p2);

                Clause new_clause2 = {yes_p1, not_helper};
                cnf_clauses.push_back(new_clause2);

                if(export_proof){
                    helper_map[not_helper->id].push_back({yes_p1});

                    sat_constraint_clauses.push_back(new_clause2);
                }

                new_clause2 = {yes_p2, not_helper};
                cnf_clauses.push_back(new_clause2);

                if(export_proof){
                    helper_map[not_helper->id].push_back({yes_p2});

                    sat_constraint_clauses.push_back(new_clause2);
                }

                if(export_proof){
                    helper_map[-yes_helper->id].push_back(new_clause1);
                }

                new_clause1.push_back(yes_helper);
                cnf_clauses.push_back(new_clause1);

                if(export_proof){
                    sat_constraint_clauses.push_back(new_clause1);
                }

                helpers.push_back(yes_helper);
            }
        }

        CNF temp_clauses = {helpers};
        impify(temp_clauses, r, cnf_clauses);
    }
}

// Encodes a constraint of type r => (x ∈ S), where S is a set variable
void Encoder::encode_set_in_imp(const BasicVar& x, const BasicVar& S, const BasicVar& r, CNF &cnf_clauses){
    
    auto elems = *get_set_elems(S);
    auto left = get_left(&x);
    auto right = get_right(&x);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

    if(left > elems[elems.size() - 1] || right < elems[0]){
        cnf_clauses.push_back({not_r});

        if(export_proof){
            sat_constraint_clauses.push_back({not_r});

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= " << *r.name << " 0)\n)\n";
        }
        return ;
    }

    Clause helpers;
    for(auto elem : elems){
        LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id, false, 0);
        LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id++, true, 0);
        if(elem >= left && elem <= right){    
            Clause new_clause1;

            LiteralPtr not_p1 = make_literal(LiteralType::ORDER, x.id, false, elem);
            LiteralPtr yes_p1 = make_literal(LiteralType::ORDER, x.id, true, elem); 
            LiteralPtr not_p2 = make_literal(LiteralType::ORDER, x.id, true, elem-1);
            LiteralPtr yes_p2 = make_literal(LiteralType::ORDER, x.id, false, elem-1); 
            LiteralPtr not_p3 = make_literal(LiteralType::SET_ELEM, S.id, false, elem);
            LiteralPtr yes_p3 = make_literal(LiteralType::SET_ELEM, S.id, true, elem); 
                
            new_clause1.push_back(not_p1);
            new_clause1.push_back(not_p2);
            new_clause1.push_back(not_p3);
        
            Clause new_clause2 = {yes_p1, not_helper};
            cnf_clauses.push_back(new_clause2);

            if(export_proof){
                helper_map[not_helper->id].push_back({yes_p1});

                sat_constraint_clauses.push_back(new_clause2);
            }

            new_clause2 = {yes_p2, not_helper};
            cnf_clauses.push_back(new_clause2);
            
            if(export_proof){
                helper_map[not_helper->id].push_back({yes_p2});

                sat_constraint_clauses.push_back(new_clause2);
            }

            new_clause2 = {yes_p3, not_helper};
            cnf_clauses.push_back(new_clause2);
        
            if(export_proof){
                helper_map[not_helper->id].push_back({yes_p3});

                sat_constraint_clauses.push_back(new_clause2);
            }

            new_clause1.push_back(yes_helper);
            cnf_clauses.push_back(new_clause1);
            
            if(export_proof){
                helper_map[-yes_helper->id].push_back({not_p1, not_p2, not_p3});

                sat_constraint_clauses.push_back(new_clause1);
            }

            helpers.push_back(yes_helper);
        }
    }

    CNF temp_clauses = {helpers};

    impify(temp_clauses, r, cnf_clauses);

    if(export_proof){
        set_in_imp_pairs.push_back({*x.name, *S.name, *r.name});
    }
}

// Encodes a constraint of type x =/= y
void Encoder::encode_set_ne(const BasicVar& x, const BasicVar& y, CNF &cnf_clauses){
    
    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(distinct " << *x.name << " " << *y.name << ")\n)\n";
    }
    
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);

    Clause helpers;
    while(i < (int)xs.size() && j < (int)ys.size()){

        if(xs[i] < ys[j]){
            helpers.push_back(make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]));
            i++;
        } else if(xs[i] > ys[j]){
            helpers.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]));
            j++;
        } else {

            LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
            LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);

            cnf_clauses.push_back({yes_x, yes_y, not_helper});
            cnf_clauses.push_back({not_x, not_y, not_helper});

            helpers.push_back(yes_helper);          
            i++; j++;

            if(export_proof){
                helper_map[not_helper->id].push_back({yes_x, yes_y});
                helper_map[not_helper->id].push_back({not_x, not_y});

                sat_constraint_clauses.push_back({yes_x, yes_y, not_helper});
                sat_constraint_clauses.push_back({not_x, not_y, not_helper});               
            }
        }
    }


    while(i < (int)xs.size())
        helpers.push_back(make_literal(LiteralType::SET_ELEM, x.id, true, xs[i++]));

    
    while(j < (int)ys.size())
        helpers.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, ys[j++]));
    

    cnf_clauses.push_back(helpers);

    if(export_proof){
        definition_clauses.push_back(helpers);
        sat_constraint_clauses.push_back(helpers);
    }
}

// Encodes a constraint of type (x =/= y) <=> r
void Encoder::encode_set_ne_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r,CNF &cnf_clauses){
    if(export_proof){

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (distinct " 
                                     << *x.name << " " << *y.name << ") 1 0))\n)\n";
    }
    
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

    Clause helpers;
    while(i < (int)xs.size() && j < (int)ys.size()){

        if(xs[i] < ys[j]){
            helpers.push_back(make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]));
            i++;
        } else if(xs[i] > ys[j]){
            helpers.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]));
            j++;
        } else {

            LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
            LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);

            cnf_clauses.push_back({yes_x, yes_y, not_helper});
            cnf_clauses.push_back({not_x, not_y, not_helper});
            cnf_clauses.push_back({yes_x, not_y, yes_helper});
            cnf_clauses.push_back({not_x, yes_y, yes_helper});
            helpers.push_back(yes_helper);          
            i++; j++;

            if(export_proof){
                helper_map[yes_helper->id].push_back({yes_x, yes_y});
                helper_map[yes_helper->id].push_back({not_x, not_y});
                helper_map[-yes_helper->id].push_back({yes_x, not_y});
                helper_map[-yes_helper->id].push_back({not_x, yes_y});

                sat_constraint_clauses.push_back({yes_x, yes_y, not_helper});
                sat_constraint_clauses.push_back({not_x, not_y, not_helper});
                sat_constraint_clauses.push_back({yes_x, not_y, yes_helper});
                sat_constraint_clauses.push_back({not_x, yes_y, yes_helper});
            }

        }
    }

    while(i < (int)xs.size())
        helpers.push_back(make_literal(LiteralType::SET_ELEM, x.id, true, xs[i++]));

    while(j < (int)ys.size())
        helpers.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, ys[j++]));

    CNF temp_clauses = {helpers};
    reify(temp_clauses, r, cnf_clauses);


}

// Encodes a constraint of type r => (x =/= y)
void Encoder::encode_set_ne_imp(const BasicVar& x, const BasicVar& y, const BasicVar& r,CNF &cnf_clauses){
    if(export_proof){

        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (distinct " 
                                     << *x.name << " " << *y.name << "))\n)\n";
    }
    
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);
    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

    Clause helpers;
    while(i < (int)xs.size() && j < (int)ys.size()){

        if(xs[i] < ys[j]){
            helpers.push_back(make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]));
            i++;
        } else if(xs[i] > ys[j]){
            helpers.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]));
            j++;
        } else {

            LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
            LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);

            cnf_clauses.push_back({yes_x, yes_y, not_helper});
            cnf_clauses.push_back({not_x, not_y, not_helper});
            cnf_clauses.push_back({yes_x, not_y, yes_helper});
            cnf_clauses.push_back({not_x, yes_y, yes_helper});
            helpers.push_back(yes_helper);          
            i++; j++;

            if(export_proof){
                helper_map[yes_helper->id].push_back({yes_x, yes_y});
                helper_map[yes_helper->id].push_back({not_x, not_y});
                helper_map[-yes_helper->id].push_back({yes_x, not_y});
                helper_map[-yes_helper->id].push_back({not_x, yes_y});

                sat_constraint_clauses.push_back({yes_x, yes_y, not_helper});
                sat_constraint_clauses.push_back({not_x, not_y, not_helper});
                sat_constraint_clauses.push_back({yes_x, not_y, yes_helper});
                sat_constraint_clauses.push_back({not_x, yes_y, yes_helper});
            }

        }
    }

    while(i < (int)xs.size())
        helpers.push_back(make_literal(LiteralType::SET_ELEM, x.id, true, xs[i++]));

    while(j < (int)ys.size())
        helpers.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, ys[j++]));

    CNF temp_clauses = {helpers};
    impify(temp_clauses, r, cnf_clauses);

}

// Encodes a constraint of type r = x ∩ y
void Encoder::encode_set_intersect(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){

    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (bvand " << *x.name << " " << *y.name << "))\n)\n";  
    }

    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    auto rs = *get_set_elems(r);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            if(check_if_val_in_domain(rs, xs[i])){
                LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
            
                cnf_clauses.push_back({not_r});       

                if(export_proof)
                    sat_constraint_clauses.push_back({not_r});
            }     
            i++;
        } else if(xs[i] > ys[j]){
            if(check_if_val_in_domain(rs, ys[j])){
                LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
            
                cnf_clauses.push_back({not_r});    

                if(export_proof)
                    sat_constraint_clauses.push_back({not_r});
            }
            j++;
        } else {
            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, xs[i]);
            LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, xs[i]);
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
            
            if(!check_if_val_in_domain(rs, xs[i])){
                cnf_clauses.push_back({not_x, not_y});

                if(export_proof)
                    sat_constraint_clauses.push_back({not_x, not_y});
            
            } else {
                cnf_clauses.push_back({not_r, yes_x});
                cnf_clauses.push_back({not_r, yes_y});
                cnf_clauses.push_back({yes_r, not_x, not_y});

                sat_constraint_clauses.push_back({not_r, yes_x});
                sat_constraint_clauses.push_back({not_r, yes_y});
                sat_constraint_clauses.push_back({yes_r, not_x, not_y});
            }
            
            i++; j++;
        }
    }

    while(i < (int)xs.size()){
        if(check_if_val_in_domain(rs, xs[i])){
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
            
            cnf_clauses.push_back({not_r});       
        
            if(export_proof)
                sat_constraint_clauses.push_back({not_r});
        }       
        i++;
    }

    while(j < (int)ys.size()){
        if(check_if_val_in_domain(rs, ys[j])){
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
            
            cnf_clauses.push_back({not_r});    
        
            if(export_proof)
                sat_constraint_clauses.push_back({not_r});
        }
        j++;
    }

    for(int i = 0; i < (int)rs.size(); i++){
        if(!binary_search(xs.begin(), xs.end(), rs[i]) || !binary_search(ys.begin(), ys.end(), rs[i])){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, r.id, false, rs[i])});

            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, r.id, false, rs[i])});
        }
    }

}

void Encoder::set_max(const BasicVar& x, const BasicVar& set, CNF &cnf_clauses){

    if(export_proof){
        connection2step << "(= " << *x.name << " (leftmost_one " << *set.name << "))\n";
        connection2step << "---" << endl;
                    
        constraints2step2 << "(= " << *x.name << " (leftmost_one " << *set.name << "))\n";

        smt_step1_funs << "(define-fun f_" << *x.name << " () Int\n";
        smt_step1_funs << "(leftmost_one " << *set.name << ")\n)\n";    
                          
        left_total_step1 << "(= " << *x.name << " f_" << *x.name << ")\n"; 
    }

    auto elems = *get_set_elems(set);

    auto yes_empty_clause_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
    auto not_empty_clause_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

    Clause helpers;
    for(auto elem : elems){
        auto yes_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        auto not_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, set.id, false, elem), 
                               make_literal(LiteralType::ORDER, x.id, false, elem-1)});  
                               
        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, set.id, true, elem), not_helper}); 
        cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, elem), not_helper}); 

        if(export_proof){
            helper_map[not_helper->id].push_back({make_literal(LiteralType::SET_ELEM, set.id, true, elem)}); 
            helper_map[not_helper->id].push_back({make_literal(LiteralType::ORDER, x.id, true, elem)});

            sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, set.id, false, elem), 
                                make_literal(LiteralType::ORDER, x.id, false, elem-1)});  
                                
            sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, set.id, true, elem), not_helper}); 
            sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, elem), not_helper});
        }

        helpers.push_back(yes_helper);

        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, set.id, false, elem), not_empty_clause_helper});
        if(export_proof){
            helper_map[not_empty_clause_helper->id].push_back({make_literal(LiteralType::SET_ELEM, set.id, false, elem)});
        
            sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, set.id, false, elem), not_empty_clause_helper});
        
        }
    }

    cnf_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, bv_left-1), not_empty_clause_helper});

    if(export_proof){
        helper_map[not_empty_clause_helper->id].push_back({make_literal(LiteralType::ORDER, x.id, true, bv_left-1)});
    
        sat_constraint_clauses.push_back({make_literal(LiteralType::ORDER, x.id, true, bv_left-1), not_empty_clause_helper});
    
    }

    helpers.push_back(yes_empty_clause_helper);
    cnf_clauses.push_back(helpers);

    if(export_proof){
        sat_constraint_clauses.push_back(helpers);

        definition_clauses.push_back(helpers);
    }
}

// Encodes a constraint of type x <= y
void Encoder::encode_set_le(const BasicVar& x, const BasicVar& y, CNF &cnf_clauses){


    auto x_elems = *get_set_elems(x);
    auto y_elems = *get_set_elems(y);
    int n = x_elems.size();
    int m = y_elems.size();

    if(x_elems.size() == 0){
        LiteralPtr yes_helper = make_literal(LiteralType::HELPER, next_helper_id, true, 0);
        LiteralPtr not_helper = make_literal(LiteralType::HELPER, next_helper_id++, false, 0);

        cnf_clauses.push_back({yes_helper, not_helper});
     
        if(export_proof){
            sat_constraint_clauses.push_back({yes_helper, not_helper});
        
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(or (prefix " << *x.name << " " << *y.name << ") "
                            << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                            << "(bvule (rev " << *y.name << ") (rev " << *x.name << "))))\n)\n";
        }

        return;
    }
    if(y_elems.size() == 0){
        if(export_proof){
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(or (prefix " << *x.name << " " << *y.name << ") "
                            << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                            << "(bvule (rev " << *y.name << ") (rev " << *x.name << "))))\n)\n";
        }

        for(auto elem : x_elems){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, elem)});

            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, elem)});
        }

        return;
    }


    if(export_proof){
        is2step = true;
        needLex = true;
        isLIA = true;
        
        constraint2step_set.insert(next_constraint_num);


        constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
        constraints2step1 << "(or (prefix " << *x.name << " " << *y.name << ") "
                          << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                          << "(bvule (rev " << *y.name << ") (rev " << *x.name << "))))\n)\n";

        constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        constraints2step2 << "(and\n";
    }


    int l = x_elems[0] < y_elems[0] ? x_elems[0] : y_elems[0];
    int u = x_elems[n-1] > y_elems[m-1] ? x_elems[n-1] : y_elems[m-1];

    auto xmax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);
    auto ymax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);

    set_max(*xmax, x, cnf_clauses);
    set_max(*ymax, y, cnf_clauses);

    if(export_proof){
        int bv_diff = bv_right - bv_left + 1;

        constraints2step2 << "(or\n(= " << *x.name << " " << *y.name << ")\n";

        string bv_left_string = (bv_left < 0) ? "(- " + to_string(-bv_left) + ")" : to_string(bv_left);
        constraints2step2 << "(ite (= (bvand (bvlshr " << *x.name << " ((_ int2bv " 
                          << bv_diff << ") (- (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << bv_left_string << "))) (_ bv1 " << bv_diff 
                          << ")) (_ bv1 " << bv_diff << "))\n(< (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << *ymax->name << ")\n(< " << *xmax->name 
                          <<  " (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")))\n)\n)\n)\n)\n";
    }

    Clause x_yes_helpers, x_not_helpers;
    Clause y_yes_helpers, y_not_helpers;

    for(int i = l; i <= u; i++){
        x_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        x_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
        y_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        y_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));

        bool x_found = false;
        bool y_found = false;

        for(auto x_elem : x_elems){
            if(x_elem == i){
                x_found = true;
                break;
            } 
        }

        for(auto y_elem : y_elems){
            if(y_elem == i){
                y_found = true;
                break;
            } 
        }

        if(x_found){
            cnf_clauses.push_back({x_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, false, i)});
            cnf_clauses.push_back({x_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, true, i)});

            if(export_proof){
                helper_map[-x_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, true, i)});

                sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, true, i)});                
            }
        } else {
            cnf_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});

            if(export_proof){
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
            }
        }

        if(y_found){
            cnf_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            cnf_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});

        if(export_proof){
            helper_map[-y_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            sat_constraint_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});            
        }
        } else {
            cnf_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});

            if(export_proof){
                helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
            }
        }
    }

    Clause yes_helpers, not_helpers;

    for(int i = l; i <= u; i++){
        yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
    }

    for(int i = l; i < u; i++){


        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
                               

        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l+1]});                           
            helper_map[not_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l+1]});  


            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
        }

        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

        if(export_proof){
            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, false, i-1)});            

        }

        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});        


        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            helper_map[-yes_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});            
        }
    }

    cnf_clauses.push_back({not_helpers[u-l],
                           x_not_helpers[u-l],
                           y_yes_helpers[u-l]});

    cnf_clauses.push_back({yes_helpers[u-l],
                           x_yes_helpers[u-l]});

    cnf_clauses.push_back({yes_helpers[u-l],
                           y_not_helpers[u-l]});

    cnf_clauses.push_back({yes_helpers[0]});

    if(export_proof){
        helper_map[not_helpers[u-l]->id].push_back({x_not_helpers[u-l], y_yes_helpers[u-l]});
        helper_map[-yes_helpers[u-l]->id].push_back({x_yes_helpers[u-l]});
        helper_map[-yes_helpers[u-l]->id].push_back({y_not_helpers[u-l]});

        sat_constraint_clauses.push_back({not_helpers[u-l],
                           x_not_helpers[u-l],
                           y_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[u-l],
                            x_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[u-l],
                            y_not_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[0]});    
        definition_clauses.push_back({yes_helpers[0]});  
    }
}

// Encodes a constraint of type (x <= y) <=> r
void Encoder::encode_set_le_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){


    auto x_elems = *get_set_elems(x);
    auto y_elems = *get_set_elems(y);
    int n = x_elems.size();
    int m = y_elems.size();

    if(x_elems.size() == 0){
        LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);

        cnf_clauses.push_back({yes_r});
     
        if(export_proof){
            sat_constraint_clauses.push_back({yes_r});
        
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= " << *r.name << " (ite (or (prefix " << *x.name << " " 
                                         << *y.name << ") " << "(and (not (prefix " 
                                         << *y.name << " " << *x.name << ")) " 
                                         << "(bvule (rev " << *y.name << ") (rev " << *x.name << ")))) 1 0))\n)\n";
        }

        return;
    }
    if(y_elems.size() == 0){
        if(export_proof){
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= " << *r.name << " (ite (or (prefix " << *x.name << " " 
                                         << *y.name << ") " << "(and (not (prefix " 
                                         << *y.name << " " << *x.name << ")) " 
                                         << "(bvule (rev " << *y.name << ") (rev " << *x.name << ")))) 1 0))\n)\n";
        }

        CNF temp_clauses;

        for(auto elem : x_elems){
            temp_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, elem)});
        }

        reify(temp_clauses, r, cnf_clauses);

        return;
    }


    if(export_proof){
        is2step = true;
        needLex = true;
        isLIA = true;
        
        constraint2step_set.insert(next_constraint_num);


        constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
        constraints2step1 << "(= " << *r.name << " (ite (or (prefix " << *x.name << " " << *y.name << ") "
                          << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                          << "(bvule (rev " << *y.name << ") (rev " << *x.name << ")))) 1 0))\n)\n";

        constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        constraints2step2 << "(and\n";
    }


    int l = x_elems[0] < y_elems[0] ? x_elems[0] : y_elems[0];
    int u = x_elems[n-1] > y_elems[m-1] ? x_elems[n-1] : y_elems[m-1];

    auto xmax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);
    auto ymax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);

    set_max(*xmax, x, cnf_clauses);
    set_max(*ymax, y, cnf_clauses);

    if(export_proof){
        int bv_diff = bv_right - bv_left + 1;

        constraints2step2 << "(= " << *r.name << " (ite (or\n(= " << *x.name << " " << *y.name << ")\n";

        string bv_left_string = (bv_left < 0) ? "(- " + to_string(-bv_left) + ")" : to_string(bv_left);
        constraints2step2 << "(ite (= (bvand (bvlshr " << *x.name << " ((_ int2bv " 
                          << bv_diff << ") (- (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << bv_left_string << "))) (_ bv1 " << bv_diff 
                          << ")) (_ bv1 " << bv_diff << "))\n(< (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << *ymax->name << ")\n(< " << *xmax->name 
                          <<  " (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << "))))\n) 1 0)))\n)\n";
    }

    Clause x_yes_helpers, x_not_helpers;
    Clause y_yes_helpers, y_not_helpers;

    for(int i = l; i <= u; i++){
        x_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        x_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
        y_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        y_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));

        bool x_found = false;
        bool y_found = false;

        for(auto x_elem : x_elems){
            if(x_elem == i){
                x_found = true;
                break;
            } 
        }

        for(auto y_elem : y_elems){
            if(y_elem == i){
                y_found = true;
                break;
            } 
        }

        if(x_found){
            cnf_clauses.push_back({x_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, false, i)});
            cnf_clauses.push_back({x_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, true, i)});

            if(export_proof){
                helper_map[-x_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, true, i)});

                sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, true, i)});                
            }
        } else {
            cnf_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});

            if(export_proof){
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
            }
        }

        if(y_found){
            cnf_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            cnf_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});

        if(export_proof){
            helper_map[-y_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            sat_constraint_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});            
        }
        } else {
            cnf_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});

            if(export_proof){
                helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
            }
        }
    }

    Clause yes_helpers, not_helpers;

    for(int i = l; i <= u; i++){
        yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
    }

    for(int i = l; i < u; i++){


        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
                               

        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l+1]});                           
            helper_map[not_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l+1]});  


            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
        }

        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

        if(export_proof){
            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, false, i-1)});            

        }

        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});        


        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            helper_map[-yes_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});            
        }
    }

    cnf_clauses.push_back({not_helpers[u-l],
                           x_not_helpers[u-l],
                           y_yes_helpers[u-l]});

    cnf_clauses.push_back({yes_helpers[u-l],
                           x_yes_helpers[u-l]});

    cnf_clauses.push_back({yes_helpers[u-l],
                           y_not_helpers[u-l]});

    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({yes_helpers[0], not_r});
    cnf_clauses.push_back({not_helpers[0], yes_r});

    if(export_proof){
        helper_map[not_helpers[u-l]->id].push_back({x_not_helpers[u-l], y_yes_helpers[u-l]});
        helper_map[-yes_helpers[u-l]->id].push_back({x_yes_helpers[u-l]});
        helper_map[-yes_helpers[u-l]->id].push_back({y_not_helpers[u-l]});

        sat_constraint_clauses.push_back({not_helpers[u-l],
                           x_not_helpers[u-l],
                           y_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[u-l],
                            x_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[u-l],
                            y_not_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[0], not_r});
        sat_constraint_clauses.push_back({not_helpers[0], yes_r});    
        definition_clauses.push_back({yes_helpers[0], not_r});
        definition_clauses.push_back({not_helpers[0], yes_r});
    }
}

// Encodes a constraint of type (x <= y) => r
void Encoder::encode_set_le_imp(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){


    auto x_elems = *get_set_elems(x);
    auto y_elems = *get_set_elems(y);
    int n = x_elems.size();
    int m = y_elems.size();

    if(x_elems.size() == 0){
        LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
        LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

        cnf_clauses.push_back({yes_r, not_r});
     
        if(export_proof){
            sat_constraint_clauses.push_back({yes_r, not_r});
        
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (or (prefix " << *x.name << " " 
                                         << *y.name << ") " << "(and (not (prefix " 
                                         << *y.name << " " << *x.name << ")) " 
                                         << "(bvule (rev " << *y.name << ") (rev " << *x.name << ")))))\n)\n";
       }

        return;
    }
    if(y_elems.size() == 0){
        if(export_proof){
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (or (prefix " << *x.name << " " 
                                         << *y.name << ") " << "(and (not (prefix " 
                                         << *y.name << " " << *x.name << ")) " 
                                         << "(bvule (rev " << *y.name << ") (rev " << *x.name << ")))))\n)\n";
        }

        CNF temp_clauses;

        for(auto elem : x_elems){
            temp_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, elem)});
        }

        impify(temp_clauses, r, cnf_clauses);

        return;
    }


    if(export_proof){
        is2step = true;
        needLex = true;
        isLIA = true;
        
        constraint2step_set.insert(next_constraint_num);


        constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
        constraints2step1 << "(=> (= " << *r.name << " 1) (or (prefix " << *x.name << " " << *y.name << ") "
                          << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                          << "(bvule (rev " << *y.name << ") (rev " << *x.name << ")))))\n)\n";

        constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        constraints2step2 << "(and\n";
    }


    int l = x_elems[0] < y_elems[0] ? x_elems[0] : y_elems[0];
    int u = x_elems[n-1] > y_elems[m-1] ? x_elems[n-1] : y_elems[m-1];

    auto xmax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);
    auto ymax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);

    set_max(*xmax, x, cnf_clauses);
    set_max(*ymax, y, cnf_clauses);

    if(export_proof){
        int bv_diff = bv_right - bv_left + 1;

        constraints2step2 << "(=> (= " << *r.name << " 1) (or\n(= " << *x.name << " " << *y.name << ")\n";

        string bv_left_string = (bv_left < 0) ? "(- " + to_string(-bv_left) + ")" : to_string(bv_left);
        constraints2step2 << "(ite (= (bvand (bvlshr " << *x.name << " ((_ int2bv " 
                          << bv_diff << ") (- (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << bv_left_string << "))) (_ bv1 " << bv_diff 
                          << ")) (_ bv1 " << bv_diff << "))\n(< (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << *ymax->name << ")\n(< " << *xmax->name 
                          <<  " (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << "))))\n)))\n)\n";
    }

    Clause x_yes_helpers, x_not_helpers;
    Clause y_yes_helpers, y_not_helpers;

    for(int i = l; i <= u; i++){
        x_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        x_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
        y_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        y_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));

        bool x_found = false;
        bool y_found = false;

        for(auto x_elem : x_elems){
            if(x_elem == i){
                x_found = true;
                break;
            } 
        }

        for(auto y_elem : y_elems){
            if(y_elem == i){
                y_found = true;
                break;
            } 
        }

        if(x_found){
            cnf_clauses.push_back({x_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, false, i)});
            cnf_clauses.push_back({x_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, true, i)});

            if(export_proof){
                helper_map[-x_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, true, i)});

                sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, true, i)});                
            }
        } else {
            cnf_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});

            if(export_proof){
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
            }
        }

        if(y_found){
            cnf_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            cnf_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});

        if(export_proof){
            helper_map[-y_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            sat_constraint_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});            
        }
        } else {
            cnf_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});

            if(export_proof){
                helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
            }
        }
    }

    Clause yes_helpers, not_helpers;

    for(int i = l; i <= u; i++){
        yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
    }

    for(int i = l; i < u; i++){


        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
                               

        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l+1]});                           
            helper_map[not_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l+1]});  


            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
        }

        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

        if(export_proof){
            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, false, i-1)});            

        }

        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});        


        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            helper_map[-yes_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});            
        }
    }

    cnf_clauses.push_back({not_helpers[u-l],
                           x_not_helpers[u-l],
                           y_yes_helpers[u-l]});

    cnf_clauses.push_back({yes_helpers[u-l],
                           x_yes_helpers[u-l]});

    cnf_clauses.push_back({yes_helpers[u-l],
                           y_not_helpers[u-l]});

    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({yes_helpers[0], not_r});

    if(export_proof){
        helper_map[not_helpers[u-l]->id].push_back({x_not_helpers[u-l], y_yes_helpers[u-l]});
        helper_map[-yes_helpers[u-l]->id].push_back({x_yes_helpers[u-l]});
        helper_map[-yes_helpers[u-l]->id].push_back({y_not_helpers[u-l]});

        sat_constraint_clauses.push_back({not_helpers[u-l],
                           x_not_helpers[u-l],
                           y_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[u-l],
                            x_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[u-l],
                            y_not_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[0], not_r}); 
        definition_clauses.push_back({yes_helpers[0], not_r});
    }
}


// Encodes a constraint of type x < y
void Encoder::encode_set_lt(const BasicVar& x, const BasicVar& y, CNF &cnf_clauses){
    auto x_elems = *get_set_elems(x);
    auto y_elems = *get_set_elems(y);
    int n = x_elems.size();
    int m = y_elems.size();

    if(y_elems.size() == 0){
        if(export_proof){
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(or (and (prefix " << *x.name << " " << *y.name << ") "
                            << " (distinct " << *x.name << " " << *y.name << ")) "
                            << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                            << "(bvult (rev " << *y.name << ") (rev " << *x.name << "))))\n)\n";
        }

        declare_unsat(cnf_clauses);

        return;
    }

    if(x_elems.size() == 0){
     
        if(export_proof){
        
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(or (and (prefix " << *x.name << " " << *y.name << ") "
                            << " (distinct " << *x.name << " " << *y.name << ")) "
                            << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                            << "(bvult (rev " << *y.name << ") (rev " << *x.name << "))))\n)\n";
        }

        Clause c;
        for(auto elem : y_elems){
            c.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, elem));
        }

        cnf_clauses.push_back(c);

        if(export_proof)
            sat_constraint_clauses.push_back(c);

        return;
    }


    if(export_proof){
        is2step = true;
        needLex = true;
        isLIA = true;
        
        constraint2step_set.insert(next_constraint_num);


        constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
        constraints2step1 << "(or (and (prefix " << *x.name << " " << *y.name << ") "
                          << "(distinct " << *x.name << " " << *y.name << ")) "
                          << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                          << "(bvult (rev " << *y.name << ") (rev " << *x.name << "))))\n)\n";

        constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        constraints2step2 << "(and\n";
    }


    int l = x_elems[0] < y_elems[0] ? x_elems[0] : y_elems[0];
    int u = x_elems[n-1] > y_elems[m-1] ? x_elems[n-1] : y_elems[m-1];

    auto xmax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);
    auto ymax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);

    set_max(*xmax, x, cnf_clauses);
    set_max(*ymax, y, cnf_clauses);

    if(export_proof){
        int bv_diff = bv_right - bv_left + 1;


        string bv_left_string = (bv_left < 0) ? "(- " + to_string(-bv_left) + ")" : to_string(bv_left);
        constraints2step2 << "(ite (= (bvand (bvlshr " << *x.name << " ((_ int2bv " 
                          << bv_diff << ") (- (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << bv_left_string << "))) (_ bv1 " << bv_diff 
                          << ")) (_ bv1 " << bv_diff << "))\n(< (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << *ymax->name << ")\n(< " << *xmax->name 
                          <<  " (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")))\n)\n)\n)\n";
    }

    Clause x_yes_helpers, x_not_helpers;
    Clause y_yes_helpers, y_not_helpers;

    for(int i = l; i <= u; i++){
        x_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        x_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
        y_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        y_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));

        bool x_found = false;
        bool y_found = false;

        for(auto x_elem : x_elems){
            if(x_elem == i){
                x_found = true;
                break;
            } 
        }

        for(auto y_elem : y_elems){
            if(y_elem == i){
                y_found = true;
                break;
            } 
        }

        if(x_found){
            cnf_clauses.push_back({x_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, false, i)});
            cnf_clauses.push_back({x_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, true, i)});

            if(export_proof){
                helper_map[-x_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, true, i)});

                sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, true, i)});                
            }
        } else {
            cnf_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});

            if(export_proof){
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
            }
        }

        if(y_found){
            cnf_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            cnf_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});

        if(export_proof){
            helper_map[-y_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            sat_constraint_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});            
        }
        } else {
            cnf_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});

            if(export_proof){
                helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
            }
        }
    }

    Clause yes_helpers, not_helpers;

    for(int i = l; i <= u; i++){
        yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
    }

    for(int i = l; i < u; i++){


        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
                               

        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l+1]});                           
            helper_map[not_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l+1]});  


            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
        }

        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

        if(export_proof){
            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, false, i-1)});            

        }

        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});        


        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            helper_map[-yes_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});            
        }
    }

    cnf_clauses.push_back({yes_helpers[u-l],
                           x_yes_helpers[u-l],
                           y_not_helpers[u-l]});

    cnf_clauses.push_back({not_helpers[u-l],
                           x_not_helpers[u-l]});

    cnf_clauses.push_back({not_helpers[u-l],
                           y_yes_helpers[u-l]});

    cnf_clauses.push_back({yes_helpers[0]});

    if(export_proof){
        helper_map[-yes_helpers[u-l]->id].push_back({x_yes_helpers[u-l], y_not_helpers[u-l]});
        helper_map[not_helpers[u-l]->id].push_back({x_not_helpers[u-l]});
        helper_map[not_helpers[u-l]->id].push_back({y_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[u-l],
                            x_yes_helpers[u-l],
                            y_not_helpers[u-l]});

        sat_constraint_clauses.push_back({not_helpers[u-l],
                            x_not_helpers[u-l]});

        sat_constraint_clauses.push_back({not_helpers[u-l],
                            y_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[0]});    
        definition_clauses.push_back({yes_helpers[0]});  
    }
}

// Encodes a constraint of type (x < y) <=> r
void Encoder::encode_set_lt_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){
    auto x_elems = *get_set_elems(x);
    auto y_elems = *get_set_elems(y);
    int n = x_elems.size();
    int m = y_elems.size();

    if(y_elems.size() == 0){
        if(export_proof){
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= " << *r.name << " (ite (or (and (prefix " << *x.name << " " << *y.name << ") "
                            << " (distinct " << *x.name << " " << *y.name << ")) "
                            << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                            << "(bvult (rev " << *y.name << ") (rev " << *x.name << ")))) 1 0))\n)\n";
        }

        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof)
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        return;
    }

    if(x_elems.size() == 0){
     
        if(export_proof){
        
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(= " << *r.name << " (ite (or (and (prefix " << *x.name << " " << *y.name << ") "
                            << " (distinct " << *x.name << " " << *y.name << ")) "
                            << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                            << "(bvult (rev " << *y.name << ") (rev " << *x.name << ")))) 1 0))\n)\n";
        }

        Clause c;
        for(auto elem : y_elems){
            c.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, elem));
        }

        CNF temp_clauses = {c};

        reify(temp_clauses, r, cnf_clauses);

        return;
    }


    if(export_proof){
        is2step = true;
        needLex = true;
        isLIA = true;
        
        constraint2step_set.insert(next_constraint_num);


        constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
        constraints2step1 << "(= " << *r.name << " (ite (or (and (prefix " << *x.name << " " << *y.name << ") "
                          << "(distinct " << *x.name << " " << *y.name << ")) "
                          << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                          << "(bvult (rev " << *y.name << ") (rev " << *x.name << ")))) 1 0))\n)\n";

        constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        constraints2step2 << "(and\n";
    }


    int l = x_elems[0] < y_elems[0] ? x_elems[0] : y_elems[0];
    int u = x_elems[n-1] > y_elems[m-1] ? x_elems[n-1] : y_elems[m-1];

    auto xmax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);
    auto ymax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);

    set_max(*xmax, x, cnf_clauses);
    set_max(*ymax, y, cnf_clauses);

    if(export_proof){
        int bv_diff = bv_right - bv_left + 1;


        string bv_left_string = (bv_left < 0) ? "(- " + to_string(-bv_left) + ")" : to_string(bv_left);
        constraints2step2 << "(= " << *r.name << " (ite (ite (= (bvand (bvlshr " << *x.name << " ((_ int2bv " 
                          << bv_diff << ") (- (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << bv_left_string << "))) (_ bv1 " << bv_diff 
                          << ")) (_ bv1 " << bv_diff << "))\n(< (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << *ymax->name << ")\n(< " << *xmax->name 
                          <<  " (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")))\n) 1 0))\n)\n)\n";
    }

    Clause x_yes_helpers, x_not_helpers;
    Clause y_yes_helpers, y_not_helpers;

    for(int i = l; i <= u; i++){
        x_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        x_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
        y_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        y_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));

        bool x_found = false;
        bool y_found = false;

        for(auto x_elem : x_elems){
            if(x_elem == i){
                x_found = true;
                break;
            } 
        }

        for(auto y_elem : y_elems){
            if(y_elem == i){
                y_found = true;
                break;
            } 
        }

        if(x_found){
            cnf_clauses.push_back({x_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, false, i)});
            cnf_clauses.push_back({x_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, true, i)});

            if(export_proof){
                helper_map[-x_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, true, i)});

                sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, true, i)});                
            }
        } else {
            cnf_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});

            if(export_proof){
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
            }
        }

        if(y_found){
            cnf_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            cnf_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});

        if(export_proof){
            helper_map[-y_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            sat_constraint_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});            
        }
        } else {
            cnf_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});

            if(export_proof){
                helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
            }
        }
    }

    Clause yes_helpers, not_helpers;

    for(int i = l; i <= u; i++){
        yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
    }

    for(int i = l; i < u; i++){


        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
                               

        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l+1]});                           
            helper_map[not_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l+1]});  


            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
        }

        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

        if(export_proof){
            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, false, i-1)});            

        }

        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});        


        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            helper_map[-yes_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});            
        }
    }

    cnf_clauses.push_back({yes_helpers[u-l],
                           x_yes_helpers[u-l],
                           y_not_helpers[u-l]});

    cnf_clauses.push_back({not_helpers[u-l],
                           x_not_helpers[u-l]});

    cnf_clauses.push_back({not_helpers[u-l],
                           y_yes_helpers[u-l]});

    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({yes_helpers[0], not_r});
    cnf_clauses.push_back({not_helpers[0], yes_r});

    if(export_proof){
        helper_map[-yes_helpers[u-l]->id].push_back({x_yes_helpers[u-l], y_not_helpers[u-l]});
        helper_map[not_helpers[u-l]->id].push_back({x_not_helpers[u-l]});
        helper_map[not_helpers[u-l]->id].push_back({y_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[u-l],
                            x_yes_helpers[u-l],
                            y_not_helpers[u-l]});

        sat_constraint_clauses.push_back({not_helpers[u-l],
                            x_not_helpers[u-l]});

        sat_constraint_clauses.push_back({not_helpers[u-l],
                            y_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[0], not_r});
        sat_constraint_clauses.push_back({not_helpers[0], yes_r});  
        definition_clauses.push_back({yes_helpers[0], not_r});
        definition_clauses.push_back({not_helpers[0], yes_r});
    }
}

// Encodes a constraint of type (x < y) => r
void Encoder::encode_set_lt_imp(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){
    auto x_elems = *get_set_elems(x);
    auto y_elems = *get_set_elems(y);
    int n = x_elems.size();
    int m = y_elems.size();

    if(y_elems.size() == 0){
        if(export_proof){
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (or (and (prefix " << *x.name << " " << *y.name << ") "
                            << " (distinct " << *x.name << " " << *y.name << ")) "
                            << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                            << "(bvult (rev " << *y.name << ") (rev " << *x.name << ")))))\n)\n";
        }

        cnf_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        if(export_proof)
            sat_constraint_clauses.push_back({make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0)});

        return;
    }

    if(x_elems.size() == 0){
     
        if(export_proof){
        
            needLex = true;
            isLIA = true;

            trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
            trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (or (and (prefix " << *x.name << " " << *y.name << ") "
                            << " (distinct " << *x.name << " " << *y.name << ")) "
                            << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                            << "(bvult (rev " << *y.name << ") (rev " << *x.name << ")))))\n)\n";
        }

        Clause c;
        for(auto elem : y_elems){
            c.push_back(make_literal(LiteralType::SET_ELEM, y.id, true, elem));
        }

        CNF temp_clauses = {c};

        impify(temp_clauses, r, cnf_clauses);

        return;
    }


    if(export_proof){
        is2step = true;
        needLex = true;
        isLIA = true;
        
        constraint2step_set.insert(next_constraint_num);


        constraints2step1 << "(define-fun smt_c" << next_constraint_num << "_step1 () Bool\n";
        constraints2step1 << "(=> (= " << *r.name << " 1) (or (and (prefix " << *x.name << " " << *y.name << ") "
                          << "(distinct " << *x.name << " " << *y.name << ")) "
                          << "(and (not (prefix " << *y.name << " " << *x.name << ")) " 
                          << "(bvult (rev " << *y.name << ") (rev " << *x.name << ")))))\n)\n";

        constraints2step2 << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        constraints2step2 << "(and\n";
    }


    int l = x_elems[0] < y_elems[0] ? x_elems[0] : y_elems[0];
    int u = x_elems[n-1] > y_elems[m-1] ? x_elems[n-1] : y_elems[m-1];

    auto xmax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);
    auto ymax = encode_int_range_helper_variable(bv_left-1, u, cnf_clauses, true);

    set_max(*xmax, x, cnf_clauses);
    set_max(*ymax, y, cnf_clauses);

    if(export_proof){
        int bv_diff = bv_right - bv_left + 1;


        string bv_left_string = (bv_left < 0) ? "(- " + to_string(-bv_left) + ")" : to_string(bv_left);
        constraints2step2 << "(=> (= " << *r.name << " 1) (ite (= (bvand (bvlshr " << *x.name << " ((_ int2bv " 
                          << bv_diff << ") (- (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << bv_left_string << "))) (_ bv1 " << bv_diff 
                          << ")) (_ bv1 " << bv_diff << "))\n(< (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")) " << *ymax->name << ")\n(< " << *xmax->name 
                          <<  " (rightmost_one (bvxor " 
                          << *x.name << " " << *y.name << ")))\n))\n)\n)\n";
    }

    Clause x_yes_helpers, x_not_helpers;
    Clause y_yes_helpers, y_not_helpers;

    for(int i = l; i <= u; i++){
        x_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        x_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
        y_yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        y_not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));

        bool x_found = false;
        bool y_found = false;

        for(auto x_elem : x_elems){
            if(x_elem == i){
                x_found = true;
                break;
            } 
        }

        for(auto y_elem : y_elems){
            if(y_elem == i){
                y_found = true;
                break;
            } 
        }

        if(x_found){
            cnf_clauses.push_back({x_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, false, i)});
            cnf_clauses.push_back({x_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, x.id, true, i)});

            if(export_proof){
                helper_map[-x_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, x.id, true, i)});

                sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, false, i)});
                sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                    make_literal(LiteralType::SET_ELEM, x.id, true, i)});                
            }
        } else {
            cnf_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});

            if(export_proof){
                helper_map[x_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({x_not_helpers[i-l], make_literal(LiteralType::ORDER, xmax->id, true, l-2)});
            }
        }

        if(y_found){
            cnf_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            cnf_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});

        if(export_proof){
            helper_map[-y_yes_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::SET_ELEM, y.id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, false, i)});
            sat_constraint_clauses.push_back({y_not_helpers[i-l],
                                   make_literal(LiteralType::SET_ELEM, y.id, true, i)});            
        }
        } else {
            cnf_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});

            if(export_proof){
                helper_map[y_not_helpers[i-l]->id].push_back({make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
        
                sat_constraint_clauses.push_back({y_not_helpers[i-l], make_literal(LiteralType::ORDER, ymax->id, true, l-2)});
            }
        }
    }

    Clause yes_helpers, not_helpers;

    for(int i = l; i <= u; i++){
        yes_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id, true, 0));
        not_helpers.push_back(make_literal(LiteralType::HELPER, next_helper_id++, false, 0));
    }

    for(int i = l; i < u; i++){


        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_yes_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               yes_helpers[i-l+1]});
        cnf_clauses.push_back({x_not_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               not_helpers[i-l+1]});
                               

        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l+1]});                           
            helper_map[not_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l+1]});
            helper_map[-yes_helpers[i-l]->id].push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l+1]});  


            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_yes_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                yes_helpers[i-l+1]});
            sat_constraint_clauses.push_back({x_not_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                not_helpers[i-l+1]});
        }

        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
        cnf_clauses.push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

        if(export_proof){
            helper_map[not_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            helper_map[-yes_helpers[i-l]->id].push_back({x_yes_helpers[i-l],
                               y_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, xmax->id, false, i-1)});

            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                not_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, true, i-1)});
            sat_constraint_clauses.push_back({x_yes_helpers[i-l],
                                y_not_helpers[i-l],
                                yes_helpers[i-l],
                                make_literal(LiteralType::ORDER, xmax->id, false, i-1)});            

        }

        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
        cnf_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});        


        if(export_proof){

            helper_map[not_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            helper_map[-yes_helpers[i-l]->id].push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});

            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               not_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, false, i)});
            sat_constraint_clauses.push_back({y_yes_helpers[i-l],
                               x_not_helpers[i-l],
                               yes_helpers[i-l],
                               make_literal(LiteralType::ORDER, ymax->id, true, i)});            
        }
    }

    cnf_clauses.push_back({yes_helpers[u-l],
                           x_yes_helpers[u-l],
                           y_not_helpers[u-l]});

    cnf_clauses.push_back({not_helpers[u-l],
                           x_not_helpers[u-l]});

    cnf_clauses.push_back({not_helpers[u-l],
                           y_yes_helpers[u-l]});

    LiteralPtr yes_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, true, 0);
    LiteralPtr not_r = make_literal(LiteralType::BOOL_VARIABLE, r.id, false, 0);

    cnf_clauses.push_back({yes_helpers[0], not_r});

    if(export_proof){
        helper_map[-yes_helpers[u-l]->id].push_back({x_yes_helpers[u-l], y_not_helpers[u-l]});
        helper_map[not_helpers[u-l]->id].push_back({x_not_helpers[u-l]});
        helper_map[not_helpers[u-l]->id].push_back({y_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[u-l],
                            x_yes_helpers[u-l],
                            y_not_helpers[u-l]});

        sat_constraint_clauses.push_back({not_helpers[u-l],
                            x_not_helpers[u-l]});

        sat_constraint_clauses.push_back({not_helpers[u-l],
                            y_yes_helpers[u-l]});

        sat_constraint_clauses.push_back({yes_helpers[0], not_r});
        definition_clauses.push_back({yes_helpers[0], not_r});
    }
}

// Encodes a constraint of type x ⊆ y
void Encoder::encode_set_subset(const BasicVar& x, const BasicVar& y, CNF &cnf_clauses){

    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *y.name << " (bvor " << *x.name << " " << *y.name << "))\n)\n";
    }

    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i])});

            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i])});
            i++;
        } else if(xs[i] > ys[j]){
           j++;
        } else {
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
        
            cnf_clauses.push_back({not_x, yes_y});    

            if(export_proof)
                sat_constraint_clauses.push_back({not_x, yes_y});
            i++; j++;
        }
    }

    while(i < (int)xs.size()){
        cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i])});

        if(export_proof)
            sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, x.id, false, xs[i])});
        i++;
    }
}

// Encodes a constraint of type (x ⊆ y) <=> r
void Encoder::encode_set_subset_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){

    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (ite (= " << *y.name << " (bvor " 
                                     << *x.name << " " << *y.name << ")) 1 0))\n)\n";
    }

    CNF temp_clauses;    
    if(export_proof){
        export_proof = false;
        encode_set_subset(x, y, temp_clauses);
        export_proof = true;
    } else 
        encode_set_subset(x, y, temp_clauses);

    reify(temp_clauses, r, cnf_clauses);


}

// Encodes a constraint of type  r => (x ⊆ y)
void Encoder::encode_set_subset_imp(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){

    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(=> (= " << *r.name << " 1) (= " << *y.name << " (bvor " 
                                     << *x.name << " " << *y.name << ")))\n)\n";
    }

    CNF temp_clauses;    
    if(export_proof){
        export_proof = false;
        encode_set_subset(x, y, temp_clauses);
        export_proof = true;
    } else 
        encode_set_subset(x, y, temp_clauses);

    impify(temp_clauses, r, cnf_clauses);

}


// Encodes a constraint of type x ⊇ y
void Encoder::encode_set_superset(const BasicVar& x, const BasicVar& y, CNF &cnf_clauses){
    encode_set_subset(y, x, cnf_clauses);
}

// Encodes a constraint of type (x ⊇ y) <=> r
void Encoder::encode_set_superset_reif(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){

    encode_set_subset_reif(y, x, r, cnf_clauses);

}

// Encodes a constraint of type r => (x ⊇ y)
void Encoder::encode_set_superset_imp(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){

    encode_set_subset_imp(y, x, r, cnf_clauses);

}

// Encodes a constraint of type r = x Δ y (r = (x \ y) ∪ (y \ x))
void Encoder::encode_set_symdiff(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){
    
    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (bvor (bvand " << *x.name << " (bvnot " << *y.name << "))"
                                     << " (bvand " << *y.name << " (bvnot " << *x.name << "))))\n)\n";
    }
    
    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    auto rs = *get_set_elems(r);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            if(!check_if_val_in_domain(rs, xs[i])){
                cnf_clauses.push_back({not_x});

                if(export_proof)
                    sat_constraint_clauses.push_back({not_x});
            } else {
                cnf_clauses.push_back({yes_x, not_r});
                cnf_clauses.push_back({not_x, yes_r});

                if(export_proof){
                    sat_constraint_clauses.push_back({yes_x, not_r});
                    sat_constraint_clauses.push_back({not_x, yes_r});
                }
            }            
            i++;
        } else if(xs[i] > ys[j]){
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, ys[j]);
            LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
        
            if(!check_if_val_in_domain(rs, ys[j])){
                cnf_clauses.push_back({not_y});

                if(export_proof)
                    sat_constraint_clauses.push_back({not_y});
            } else {
                cnf_clauses.push_back({yes_y, not_r});
                cnf_clauses.push_back({not_y, yes_r});

                if(export_proof){
                    sat_constraint_clauses.push_back({yes_y, not_r});
                    sat_constraint_clauses.push_back({not_y, yes_r});
                }
            }                      
            j++;
        } else {
            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, xs[i]);
            LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, xs[i]);
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            if(!check_if_val_in_domain(rs, xs[i])){
                cnf_clauses.push_back({yes_x, not_y});
                cnf_clauses.push_back({not_x, yes_y});

                if(export_proof){
                    sat_constraint_clauses.push_back({yes_x, not_y});
                    sat_constraint_clauses.push_back({not_x, yes_y});                
                }
            } else {
                cnf_clauses.push_back({not_r, yes_x, yes_y});
                cnf_clauses.push_back({not_r, not_x, not_y});
                cnf_clauses.push_back({yes_r, not_x, yes_y});
                cnf_clauses.push_back({yes_r, yes_x, not_y});

                if(export_proof){
                    sat_constraint_clauses.push_back({not_r, yes_x, yes_y});
                    sat_constraint_clauses.push_back({not_r, not_x, not_y});
                    sat_constraint_clauses.push_back({yes_r, not_x, yes_y});
                    sat_constraint_clauses.push_back({yes_r, yes_x, not_y});
                }
            }
            i++; j++;
        }
    }

    while(i < (int)xs.size()){
        LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
        LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
        LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
        LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);

        if(!check_if_val_in_domain(rs, xs[i])){
            cnf_clauses.push_back({not_x});

            if(export_proof)
                sat_constraint_clauses.push_back({not_x});
        } else {
            cnf_clauses.push_back({yes_x, not_r});
            cnf_clauses.push_back({not_x, yes_r});
            
            if(export_proof){
                sat_constraint_clauses.push_back({yes_x, not_r});
                sat_constraint_clauses.push_back({not_x, yes_r});
            }
        }
        i++;
    }

    while(j < (int)ys.size()){
        LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
        LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, ys[j]);
        LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);
        LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
    
        if(!check_if_val_in_domain(rs, ys[j])){
            cnf_clauses.push_back({not_y});

            if(export_proof)
                sat_constraint_clauses.push_back({not_y});
        } else {
            cnf_clauses.push_back({yes_y, not_r});
            cnf_clauses.push_back({not_y, yes_r});
            
            if(export_proof){
                sat_constraint_clauses.push_back({yes_y, not_r});
                sat_constraint_clauses.push_back({not_y, yes_r});
            }
        }
        j++;
    }

    for(int i = 0; i < (int)rs.size(); i++){
        if(!binary_search(xs.begin(), xs.end(), rs[i]) && !binary_search(ys.begin(), ys.end(), rs[i])){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, r.id, false, rs[i])});

            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, r.id, false, rs[i])});

        }
    }
}

// Encodes a constraint of type r = x ∪ y
void Encoder::encode_set_union(const BasicVar& x, const BasicVar& y, const BasicVar& r, CNF &cnf_clauses){


    if(export_proof){
        trivial_encoding_constraints << "(define-fun smt_c" << next_constraint_num++ << " () Bool\n";
        trivial_encoding_constraints << "(= " << *r.name << " (bvor " << *x.name << " " << *y.name << "))\n)\n";  
    }

    int i = 0, j = 0;
    auto xs = *get_set_elems(x);
    auto ys = *get_set_elems(y);
    auto rs = *get_set_elems(r);

    while(i < (int)xs.size() && j < (int)ys.size()){
        if(xs[i] < ys[j]){
            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            if(!check_if_val_in_domain(rs, xs[i])){
                cnf_clauses.push_back({not_x});

                if(export_proof)
                    sat_constraint_clauses.push_back({not_x});
            } else {
                cnf_clauses.push_back({yes_x, not_r});
                cnf_clauses.push_back({not_x, yes_r});

                if(export_proof){
                    sat_constraint_clauses.push_back({yes_x, not_r});
                    sat_constraint_clauses.push_back({not_x, yes_r});
                }
            }            
            i++;
        } else if(xs[i] > ys[j]){
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
            LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, ys[j]);
            LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
        
            if(!check_if_val_in_domain(rs, ys[j])){
                cnf_clauses.push_back({not_y});

                if(export_proof)
                    sat_constraint_clauses.push_back({not_y});
            } else {
                cnf_clauses.push_back({yes_y, not_r});
                cnf_clauses.push_back({not_y, yes_r});

                if(export_proof){
                    sat_constraint_clauses.push_back({yes_y, not_r});
                    sat_constraint_clauses.push_back({not_y, yes_r});
                }
            }  
            j++;
        } else {
            LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
            LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, xs[i]);
            LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
            LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
            LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, xs[i]);
            LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);
        
            if(!check_if_val_in_domain(rs, xs[i])){
                cnf_clauses.push_back({not_x});
                cnf_clauses.push_back({not_y});

                if(export_proof){
                    sat_constraint_clauses.push_back({not_x});
                    sat_constraint_clauses.push_back({not_y});
                }
            } else {
                cnf_clauses.push_back({yes_r, not_x});
                cnf_clauses.push_back({yes_r, not_y});
                cnf_clauses.push_back({not_r, yes_x, yes_y});
            
                if(export_proof){
                    sat_constraint_clauses.push_back({yes_r, not_x});
                    sat_constraint_clauses.push_back({yes_r, not_y});
                    sat_constraint_clauses.push_back({not_r, yes_x, yes_y});         
                }
            }   
            i++; j++;
        }
    }

    while(i < (int)xs.size()){
        LiteralPtr yes_x = make_literal(LiteralType::SET_ELEM, x.id, true, xs[i]);
        LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, xs[i]);
        LiteralPtr not_x = make_literal(LiteralType::SET_ELEM, x.id, false, xs[i]);
        LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, xs[i]);

        if(!check_if_val_in_domain(rs, xs[i])){
            cnf_clauses.push_back({not_x});

            if(export_proof)
                sat_constraint_clauses.push_back({not_x});
        } else {
            cnf_clauses.push_back({yes_x, not_r});
            cnf_clauses.push_back({not_x, yes_r});
            
            if(export_proof){
                sat_constraint_clauses.push_back({yes_x, not_r});
                sat_constraint_clauses.push_back({not_x, yes_r});
            }
        }
        i++;
    }

    while(j < (int)ys.size()){
        LiteralPtr yes_y = make_literal(LiteralType::SET_ELEM, y.id, true, ys[j]);
        LiteralPtr yes_r = make_literal(LiteralType::SET_ELEM, r.id, true, ys[j]);
        LiteralPtr not_y = make_literal(LiteralType::SET_ELEM, y.id, false, ys[j]);
        LiteralPtr not_r = make_literal(LiteralType::SET_ELEM, r.id, false, ys[j]);
    
        if(!check_if_val_in_domain(rs, ys[j])){
            cnf_clauses.push_back({not_y});

            if(export_proof)
                sat_constraint_clauses.push_back({not_y});
        } else {
            cnf_clauses.push_back({yes_y, not_r});
            cnf_clauses.push_back({not_y, yes_r});
            
            if(export_proof){
                sat_constraint_clauses.push_back({yes_y, not_r});
                sat_constraint_clauses.push_back({not_y, yes_r});
            }
        }
        j++;
    }

    for(int i = 0; i < (int)rs.size(); i++){
        if(!binary_search(xs.begin(), xs.end(), rs[i]) && !binary_search(ys.begin(), ys.end(), rs[i])){
            cnf_clauses.push_back({make_literal(LiteralType::SET_ELEM, r.id, false, rs[i])});

            if(export_proof)
                sat_constraint_clauses.push_back({make_literal(LiteralType::SET_ELEM, r.id, false, rs[i])});

        }
    }

}