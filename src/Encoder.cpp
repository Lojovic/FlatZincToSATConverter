#include "Encoder.hpp"

Encoder::Encoder(const std::vector<Item> &items) : items(items) {}

// Declares the problem to be unsat
void Encoder::declare_unsat(){
    std::cout << "UNSAT" << std::endl;
    unsat = true;
}

// Passes through the list of items which constitute the problem
// and calls the appropriate encoder function
std::vector<std::vector<std::string>> Encoder::encode_to_cnf() {

    for (const auto& item : items) {
            if(unsat)
                break;
            else if(is<Parameter>(item))
                encode_parameter(as<Parameter>(item), cnf_clauses);
            else if(is<Variable>(item))
                encode_variable(as<Variable>(item), cnf_clauses);
            else if(is<Array>(item))
                encode_array(as<Array>(item), cnf_clauses);
            else if(is<Constraint>(item))
                encode_constraint(as<Constraint>(item), cnf_clauses);
            else if(is<Predicate>(item))
                encode_predicate(as<Predicate>(item), cnf_clauses);
            else{
                std::cerr << "Unknown item type in encoder" << std::endl;
                break;
            }
    }

    return cnf_clauses;
}

// Converts the encoded problem to the DIMACS format
// and writes the output to the file named fileName
void Encoder::write_to_file(std::string fileName){

    std::ofstream file(fileName);

    if (!file.is_open()){
        std::cerr << "Cannot open file" << std::endl;
        return;
    }    

    //TODO nadji pametniji nacin, ovo je hack
    file << "                                                   " << std::endl;
    for(const auto& c : cnf_clauses) {
        for(const auto &l : c){
            bool sign = l[0] == '-';

            std::string l1;
            if(sign)
                l1 = l.substr(1);
            else
                l1 = l;

            if(literal_to_num.find(l1) == literal_to_num.end()){
                literal_to_num[l1] = next_dimacs_num++;
                if(l1[0] == 'p')
                    num_to_literal[next_dimacs_num-1] = l;
            } 

            file << (sign ? -literal_to_num[l1] : literal_to_num[l1]) << " ";
        }
        file << 0 << std::endl;
    }    

    file.seekp(0, std::ios::beg);
    file << "p cnf " << next_dimacs_num - 1  << " " << cnf_clauses.size() << std::endl;

}

// Runs the MiniSat solver by executing the appropriate system call.
// The input in DIMACS format should be in the inputFile, and the output is
// written to the outputFile
void Encoder::run_minisat(const std::string& inputFile, const std::string& outputFile) {

    std::string command = "minisat " + inputFile + " " + outputFile +  "> /dev/null 2>&1";

    std::system(command.c_str());
}

// Reads the MiniSat solver output, converts it to a human readable format
// and writes the output to std::cout
void Encoder::read_minisat_output(const std::string& outputFile) {
    std::ifstream output(outputFile);
    if (!output.is_open()) {
        std::cerr << "Cannot open file" << std::endl;
        return;
    }

    std::string sat;
    output >> sat;
    if(sat == "UNSAT"){
        declare_unsat();
        return;
    }

    std::cout << "SAT" << std::endl;

    int curr_lit_num;
    while (output >> curr_lit_num) {

        bool sign = false;
        if(curr_lit_num < 0){
            sign = true;
            curr_lit_num = -curr_lit_num;
        }

        if(num_to_literal.find(curr_lit_num) == num_to_literal.end())
            continue;

        auto literal = num_to_literal[curr_lit_num];
        std::regex regex("p_var(\\d+)_(-?\\d+)");
        std::smatch match;

        int id, val;

        if (std::regex_search(literal, match, regex)) {
            id = std::stoi(match[1]);
            val = std::stoi(match[2]);
        } else {
            std::cerr << "No match found" << std::endl;
            return;
        }

        if(id_map.find(id) == id_map.end())
            continue;

        IntRangeVar curr_var = as<IntRangeVar>(id_map[id]);

        if(!sign){
            if(curr_var.right > val)
                curr_var.right = val;
        } else {
            if(curr_var.left < val + 1)
                curr_var.left = val + 1;
        }

        id_map[id] = curr_var;

        if(curr_var.left == curr_var.right){
            std::cout << curr_var.name << " = " << curr_var.left << std::endl;
            id_map.erase(id);
        } 

    }

    output.close();
}

// Parses an array of coefficients for linear constraints
std::vector<int> Encoder::parse_coefs(const std::string &array){

    std::vector<int> result;

    std::stringstream ss(array);
    std::string item;
    
    while (std::getline(ss, item, ',')) {
        item.erase(0, item.find_first_not_of(" \t"));
        item.erase(item.find_last_not_of(" \t") + 1);
        
        result.push_back(std::stoi(item));
    }
    
    return result;
}

// Parses an array of variables for linear constraints
std::vector<IntRangeVarOrInt> Encoder::parse_vars(const std::string &array){

    std::vector<IntRangeVarOrInt> result;

    std::stringstream ss(array);
    std::string item;
    
    while (std::getline(ss, item, ',')) {
        item.erase(0, item.find_first_not_of(" \t"));
        item.erase(item.find_last_not_of(" \t") + 1);

        //TODO check if this works ok
        if(typeid(item) == typeid(int))
            result.push_back(std::stoi(item));
        else
            result.push_back(as<IntRangeVar>(variable_map[item]));
        
    }
    
    return result;
}

// Encodes a parameter of the model 
void Encoder::encode_parameter(const Parameter& param, std::vector<std::vector<std::string>>& cnf_clauses) {

    if (param.type == "int") {
        
        parameter_map[param.name] = IntParameter{param.name, stoi(param.value)}; 
    } else if (param.type == "bool") {

        if(param.value == "true")
            parameter_map[param.name] = BoolParameter{param.name, true};  
        else
            parameter_map[param.name] = BoolParameter{param.name, false};  
    }
    //TODO encode int range, parse for ..

}

// Encodes a variable based on it's type.
//TODO add reverse map for all
void Encoder::encode_variable(const Variable& var, std::vector<std::vector<std::string>>& cnf_clauses) {
    int new_var_id = next_var_id++;
    if (var.type == "int") {
        
        variable_map[var.name] = IntVar{var.name, new_var_id, stoi(var.value)}; 
    
    } else if (var.type == "bool") {

        variable_map[var.name] = BoolVar{var.name, new_var_id};  
    
    } else if (var.type == "int_range"){
        
        int pos = var.value.find("..");

        int left = std::stoi(var.value.substr(0, pos));
        int right = std::stoi(var.value.substr(pos + 2));

        variable_map[var.name] = IntRangeVar{var.name, new_var_id, left, right}; 
        id_map[new_var_id] = variable_map[var.name];

        std::vector<std::string> clause1, clause2, curr_clause;
        clause1 = {std::format("-p_var{}_{}", new_var_id, left - 1)};
        clause2 = {std::format("p_var{}_{}", new_var_id, right)};

        cnf_clauses.push_back(clause1);
        cnf_clauses.push_back(clause2);
        for(int i = left; i <= right; i++){
            curr_clause.push_back(std::format("-p_var{}_{}", new_var_id, i - 1));
            curr_clause.push_back(std::format("p_var{}_{}", new_var_id, i));
            cnf_clauses.push_back(curr_clause);
            curr_clause.clear();
        }

    }
}

// Encodes a helper variable for substitutions
IntRangeVarOrInt Encoder::encode_helper_variable(const int left, const int right, std::vector<std::vector<std::string>>& cnf_clauses) {

    int sub_id = next_sub_id++;
    auto var = IntRangeVar{std::format("sub_{}", sub_id), sub_id, left, right};

    std::vector<std::string> clause1, clause2, curr_clause;
    clause1 = {std::format("-r_var{}_{}", sub_id, left - 1)};
    clause2 = {std::format("r_var{}_{}", sub_id, right)};

    cnf_clauses.push_back(clause1);
    cnf_clauses.push_back(clause2);
    for(int i = left; i <= right; i++){
        curr_clause.push_back(std::format("-r_var{}_{}", sub_id, i - 1));
        curr_clause.push_back(std::format("r_var{}_{}", sub_id, i));
        cnf_clauses.push_back(curr_clause);
        curr_clause.clear();
    }    

    return var;
}

// Checks which constraint is in question and calls the
// appropriate function to encode it
void Encoder::encode_constraint(const Constraint& constr, std::vector<std::vector<std::string>>& cnf_clauses) {
    
    
    if(constr.name == "int_abs"){
        IntRangeVar a = as<IntRangeVar>(variable_map[constr.var1]);
        IntRangeVar b = as<IntRangeVar>(variable_map[constr.var2]);
        encode_int_abs(a, b, cnf_clauses);
    } else if(constr.name == "int_eq"){
        IntRangeVar a = as<IntRangeVar>(variable_map[constr.var1]);
        IntRangeVar b = as<IntRangeVar>(variable_map[constr.var2]);
        encode_int_eq(a, b, cnf_clauses);
    } else if(constr.name == "int_le"){
        IntRangeVar a = as<IntRangeVar>(variable_map[constr.var1]);
        IntRangeVar b = as<IntRangeVar>(variable_map[constr.var2]);
        encode_int_le(a, b, cnf_clauses);
    } else if(constr.name == "int_lin_le"){
        std::vector<int> coefs = parse_coefs(constr.var1);
        std::vector<IntRangeVarOrInt> vars;

        if(array_map.find(constr.var2) == array_map.end())
            vars = parse_vars(constr.var2);
        else
            vars = array_map[constr.var2].elems;
        int c = std::stoi(constr.var3);
        encode_int_lin_le(coefs, vars, c, cnf_clauses);
    } else if(constr.name == "int_lt"){
        IntRangeVar a = as<IntRangeVar>(variable_map[constr.var1]);
        IntRangeVar b = as<IntRangeVar>(variable_map[constr.var2]);
        encode_int_lt(a, b, cnf_clauses);
    } else if(constr.name == "int_max"){
        IntRangeVar a = as<IntRangeVar>(variable_map[constr.var1]);
        IntRangeVar b = as<IntRangeVar>(variable_map[constr.var2]);
        IntRangeVar c = as<IntRangeVar>(variable_map[constr.var3]);
        encode_int_max(a, b, c, cnf_clauses);
    } else if(constr.name == "int_min"){
        IntRangeVar a = as<IntRangeVar>(variable_map[constr.var1]);
        IntRangeVar b = as<IntRangeVar>(variable_map[constr.var2]);
        IntRangeVar c = as<IntRangeVar>(variable_map[constr.var3]);
        encode_int_min(a, b, c, cnf_clauses);
    } else if(constr.name == "int_ne"){
        IntRangeVar a = as<IntRangeVar>(variable_map[constr.var1]);
        IntRangeVar b = as<IntRangeVar>(variable_map[constr.var2]);
        encode_int_ne(a, b, cnf_clauses);
    }

}

void Encoder::encode_predicate(const Predicate& pred, std::vector<std::vector<std::string>>& cnf_clauses) {
    //TODO ...
}

// Encodes an array of a given type (for now only IntRangeVars)
void Encoder::encode_array(const Array& array, std::vector<std::vector<std::string>>& cnf_clauses) {
    std::string name = array.name;
    
    std::vector<IntRangeVarOrInt> elems;
    for(auto elem : array.elems){
        if(typeid(elem) == typeid(int))
            elems.push_back(as<int>(elem));
        else{
            Variable temp = as<Variable>(elem);
            elems.push_back(as<IntRangeVar>(variable_map[temp.name]));
        }
    }
    array_map[name] = {name, elems};
}

// ---------------------------- Encoding constraints -------------------------------------

// Primitive comparison of type: a - b <= c
void Encoder::encode_primitive_comparison_minus(const IntRangeVar& a, const IntRangeVar& b, int c, std::vector<std::vector<std::string>>& cnf_clauses){

    if(c < a.left - b.right){
        declare_unsat();
        return ;
    } 

    std::vector<std::string> curr_clause;
    for(int i = a.left - 1; i <= a.right; i++){
        for(int j = -b.right - 1; j <= -b.left; j++)
            if(i + j == c-1){
                curr_clause.push_back(std::format("p_var{}_{}", a.var_id, i));
                curr_clause.push_back(std::format("-p_var{}_{}", b.var_id, -j - 1));
                cnf_clauses.push_back(curr_clause);
                curr_clause.clear();
            }

    }

}

// Primitive comparison of type: a + b <= c
void Encoder::encode_primitive_comparison_plus(const IntRangeVar& a, const IntRangeVar& b, int c, std::vector<std::vector<std::string>>& cnf_clauses){

    if(c < a.left + b.left){
        declare_unsat();
        return;
    }

    std::vector<std::string> curr_clause;
    for(int i = a.left - 1; i <= a.right; i++){
        for(int j = b.left - 1; j <= b.right; j++){
            if(i + j == c-1){
                curr_clause.push_back(std::format("p_var{}_{}", a.var_id, i));
                curr_clause.push_back(std::format("p_var{}_{}", b.var_id, j));
                cnf_clauses.push_back(curr_clause);
                curr_clause.clear();
            }
        }
    }

}



// Encodes a constraint of type |a| = b
void Encoder::encode_int_abs(const IntRangeVar& a, const IntRangeVar& b, std::vector<std::vector<std::string>>& cnf_clauses){
 
    encode_primitive_comparison_minus(a, b, 0, cnf_clauses);

    std::vector<std::vector<std::string>> temp_clauses;
    encode_primitive_comparison_plus(a, b, -1, temp_clauses);
    std::vector<std::vector<std::string>> new_clauses;
    std::vector<std::string> helpers;
    std::vector<std::string> new_clause;
    std::string helper;
    for(auto c : temp_clauses){
        helper = std::format("q_{}", next_helper_id++);
        for(auto lit : c){
            new_clause.push_back("-" + lit);
            new_clause.push_back("-" + helper);
            new_clauses.push_back(new_clause);
            new_clause.clear();
        }
        helpers.push_back(helper);

    }
    new_clauses.push_back(helpers);
    
    cnf_clauses.insert(cnf_clauses.end(), new_clauses.begin(), new_clauses.end());
    temp_clauses.clear();

    std::string helper1 = std::format("q_{}", next_helper_id++);
    encode_primitive_comparison_minus(b, a, 0, temp_clauses);
    int i;
    for(i = 0; i < temp_clauses.size(); i++){
        temp_clauses[i].push_back("-" + helper1);
    }

    std::string helper2 = std::format("q_{}", next_helper_id++);
    encode_primitive_comparison_plus(a, b, 0, temp_clauses);
    for(int j = i; j < temp_clauses.size(); j++){
        temp_clauses[j].push_back("-" + helper2);
    }

    temp_clauses.push_back({helper1, helper2});
    cnf_clauses.insert(cnf_clauses.end(), temp_clauses.begin(), temp_clauses.end());

}

// Encodes a constraint of type a = b
void Encoder::encode_int_eq(const IntRangeVar& a, const IntRangeVar& b, std::vector<std::vector<std::string>>& cnf_clauses){
 
    encode_primitive_comparison_minus(a, b, 0, cnf_clauses);
    encode_primitive_comparison_minus(b, a, 0, cnf_clauses);

}

// Encodes a constraint of type a <= b
void Encoder::encode_int_le(const IntRangeVar& a, const IntRangeVar& b, std::vector<std::vector<std::string>>& cnf_clauses){

    encode_primitive_comparison_minus(a, b, 0, cnf_clauses);

}

// Encodes a substitution x = a1*x2 + a2*x2
void Encoder::encode_substitution(const IntRangeVarOrInt &var, const IntRangeVarOrInt &var1, int coef1, const IntRangeVarOrInt &var2, int coef2, std::vector<std::vector<std::string>>& cnf_clauses){

    auto x = as<IntRangeVar>(var);
    auto x1 = as<IntRangeVar>(var1);
    auto x2 = as<IntRangeVar>(var2);

    std::vector<std::string> new_clause;

    //-x + x1 + x2 <= 0
    int lower_bound_x1 = (coef1 > 0) ? coef1*x1.left : coef1*x1.right;
    int upper_bound_x1 = (coef1 > 0) ? coef1*x1.right : coef1*x1.left;
    int lower_bound_x2 = (coef2 > 0) ? coef2*x2.left : coef2*x2.right;
    int upper_bound_x2 = (coef2 > 0) ? coef2*x2.right : coef2*x2.left;

    for(int i = -x.right - 1; i <= -x.left; i++){
        for(int j = lower_bound_x1 - 1; j <= upper_bound_x1; j++){
            for(int k = lower_bound_x2 - 1; k <= upper_bound_x2; k++){
                if(i + j + k == -2){
                    
                    new_clause.push_back(std::format("-r_var{}_{}", x.var_id, -i - 1));

                    if(coef1 > 0){
                        //TODO Popraviti da se proveri bolje (sa sub_)
                        if(x1.name[0] == 's')
                            new_clause.push_back(std::format("r_var{}_{}", x1.var_id, (int)floor((double)j/coef1)));
                        else
                            new_clause.push_back(std::format("p_var{}_{}", x1.var_id, (int)floor((double)j/coef1)));
                    } else {
                        if(x1.name[0] == 's')
                            new_clause.push_back(std::format("-r_var{}_{}", x1.var_id, (int)ceil((double)j/coef1) - 1));
                        else
                            new_clause.push_back(std::format("-p_var{}_{}", x1.var_id, (int)ceil((double)j/coef1) - 1));                        
                    }

                    if(coef2 > 0)
                        new_clause.push_back(std::format("p_var{}_{}", x2.var_id, (int)floor((double)k/coef2)));
                    else
                        new_clause.push_back(std::format("-p_var{}_{}", x2.var_id, (int)ceil((double)k/coef2) - 1));

                    cnf_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }    

    coef1 = -coef1;
    coef2 = -coef2;

    //x - x1 - x2 <= 0
    lower_bound_x1 = (coef1 > 0) ? coef1*x1.left : coef1*x1.right;
    upper_bound_x1 = (coef1 > 0) ? coef1*x1.right : coef1*x1.left;
    lower_bound_x2 = (coef2 > 0) ? coef2*x2.left : coef2*x2.right;
    upper_bound_x2 = (coef2 > 0) ? coef2*x2.right : coef2*x2.left;

    for(int i = x.left - 1; i <= x.right; i++){
        for(int j = lower_bound_x1 - 1; j <= upper_bound_x1; j++){
            for(int k = lower_bound_x2 - 1; k <= upper_bound_x2; k++){
                if(i + j + k == -2){

                    new_clause.push_back(std::format("r_var{}_{}", x.var_id, i));

                    if(coef1 > 0){
                        //TODO Popraviti da se proveri bolje (sa sub_)
                        if(x1.name[0] == 's')
                            new_clause.push_back(std::format("r_var{}_{}", x1.var_id, (int)floor((double)j/coef1)));
                        else
                            new_clause.push_back(std::format("p_var{}_{}", x1.var_id, (int)floor((double)j/coef1)));
                    } else {
                        if(x1.name[0] == 's')
                            new_clause.push_back(std::format("-r_var{}_{}", x1.var_id, (int)ceil((double)j/coef1) - 1));
                        else
                            new_clause.push_back(std::format("-p_var{}_{}", x1.var_id, (int)ceil((double)j/coef1) - 1));                        
                    }

                    if(coef2 > 0)
                        new_clause.push_back(std::format("p_var{}_{}", x2.var_id, (int)floor((double)k/coef2)));
                    else
                        new_clause.push_back(std::format("-p_var{}_{}", x2.var_id, (int)ceil((double)k/coef2) - 1));
                         
                
                    cnf_clauses.push_back(new_clause);
                    new_clause.clear();
                }
            }
        }
    }


}

// Encodes a constraint of type a1*x1 + a2*x2 + ... + an*xn <= c
//TODO Hendluj kad je samo jedan elem
void Encoder::encode_int_lin_le(const std::vector<int>& coefs, const std::vector<IntRangeVarOrInt> &vars, int c, std::vector<std::vector<std::string>>& cnf_clauses){

    int sum = 0;
    for(int i = 0; i < coefs.size(); i++){
        if(coefs[i] > 0)
            sum += coefs[i]*as<IntRangeVar>(vars[i]).left;
        else
            sum += coefs[i]*as<IntRangeVar>(vars[i]).right;
    }
    if(c < sum){
        declare_unsat();
        return ;
    }    

    if(vars.size() == 1){
        cnf_clauses.push_back({std::format("p_var{}_{}", as<IntRangeVar>(vars[0]).var_id, c/coefs[0])});
        return;
    }

    int lower_bound1 = coefs[0] > 0 ? as<IntRangeVar>(vars[0]).left*coefs[0] : as<IntRangeVar>(vars[0]).right*coefs[0];
    int upper_bound1 = coefs[0] > 0 ? as<IntRangeVar>(vars[0]).right*coefs[0] : as<IntRangeVar>(vars[0]).left*coefs[0]; 
    int lower_bound2 = coefs[1] > 0 ? as<IntRangeVar>(vars[1]).left*coefs[1] : as<IntRangeVar>(vars[1]).right*coefs[1];
    int upper_bound2 = coefs[1] > 0 ? as<IntRangeVar>(vars[1]).right*coefs[1] : as<IntRangeVar>(vars[1]).left*coefs[1]; 

    int lower_bound = lower_bound1 + lower_bound2;
    int upper_bound = upper_bound1 + upper_bound2;

    IntRangeVarOrInt var = encode_helper_variable(lower_bound, upper_bound, cnf_clauses);
    encode_substitution(var, vars[0], coefs[0], vars[1], coefs[1], cnf_clauses);
    IntRangeVarOrInt var1;
    for(int i = 2; i < coefs.size(); i++){
 
        lower_bound1 = as<IntRangeVar>(var).left;
        upper_bound1 = as<IntRangeVar>(var).right;
        lower_bound2 = coefs[i] > 0 ? as<IntRangeVar>(vars[i]).left*coefs[i] : as<IntRangeVar>(vars[i]).right*coefs[i];
        upper_bound2 = coefs[i] > 0 ? as<IntRangeVar>(vars[i]).right*coefs[i] : as<IntRangeVar>(vars[i]).left*coefs[i]; 
        lower_bound = lower_bound1 + lower_bound2;
        upper_bound = upper_bound1 + upper_bound2;


        var1 = encode_helper_variable(lower_bound, upper_bound, cnf_clauses);

        encode_substitution(var1, var, 1, vars[i], coefs[i], cnf_clauses);

        var = var1;
    }

    if(vars.size() == 2)
        cnf_clauses.push_back({std::format("r_var{}_{}", as<IntRangeVar>(var).var_id, c)});
    else 
        cnf_clauses.push_back({std::format("r_var{}_{}", as<IntRangeVar>(var1).var_id, c)});
}

// Encode constraint of type a < b
void Encoder::encode_int_lt(const IntRangeVar& a, const IntRangeVar& b, std::vector<std::vector<std::string>>& cnf_clauses){

    encode_primitive_comparison_minus(a, b, -1, cnf_clauses);

}

// Encode constraint of type max(a, b) = c
void Encoder::encode_int_max(const IntRangeVar& a, const IntRangeVar& b, const IntRangeVar& c, std::vector<std::vector<std::string>>& cnf_clauses){

    encode_primitive_comparison_minus(a, c, 0, cnf_clauses);
    encode_primitive_comparison_minus(b, c, 0, cnf_clauses);

    std::string helper1 = std::format("q_{}", next_helper_id++);
    std::vector<std::vector<std::string>> temp_clauses;
    encode_primitive_comparison_minus(c, a, 0, temp_clauses);
    int i;
    for(i = 0; i < temp_clauses.size(); i++){
        temp_clauses[i].push_back("-" + helper1);
    }

    std::string helper2 = std::format("q_{}", next_helper_id++);
    encode_primitive_comparison_minus(c, b, 0, temp_clauses);
    for(int j = i; j < temp_clauses.size(); j++){
        temp_clauses[j].push_back("-" + helper2);
    }

    temp_clauses.push_back({helper1, helper2});
    cnf_clauses.insert(cnf_clauses.end(), temp_clauses.begin(), temp_clauses.end());

}

// Encode constraint of type min(a, b) = c
void Encoder::encode_int_min(const IntRangeVar& a, const IntRangeVar& b, const IntRangeVar& c, std::vector<std::vector<std::string>>& cnf_clauses){
    
    encode_primitive_comparison_minus(c, a, 0, cnf_clauses);
    encode_primitive_comparison_minus(c, b, 0, cnf_clauses);

    std::string helper1 = std::format("q_{}", next_helper_id++);
    std::vector<std::vector<std::string>> temp_clauses;
    encode_primitive_comparison_minus(a, c, 0, temp_clauses);
    int i;
    for(i = 0; i < temp_clauses.size(); i++){
        temp_clauses[i].push_back("-" + helper1);
    }

    std::string helper2 = std::format("q_{}", next_helper_id++);
    encode_primitive_comparison_minus(b, c, 0, temp_clauses);
    for(int j = i; j < temp_clauses.size(); j++){
        temp_clauses[j].push_back("-" + helper2);
    }

    temp_clauses.push_back({helper1, helper2});
    cnf_clauses.insert(cnf_clauses.end(), temp_clauses.begin(), temp_clauses.end());

}

// Encode constraint of type a =/= b
void Encoder::encode_int_ne(const IntRangeVar& a, const IntRangeVar& b, std::vector<std::vector<std::string>>& cnf_clauses){


    std::string helper1 = std::format("q_{}", next_helper_id++);
    std::string helper2 = std::format("q_{}", next_helper_id++);   
    cnf_clauses.push_back({helper1, helper2});

    std::vector<std::vector<std::string>> temp_clauses; 
    encode_primitive_comparison_minus(a, b, -1, temp_clauses);

    std::vector<std::string> curr_clause;
    for(int i = 0; i < temp_clauses.size(); i++)
        temp_clauses[i].push_back("-" + helper1);

    for(auto clause : temp_clauses)
        cnf_clauses.push_back(clause);

    temp_clauses.clear();
    encode_primitive_comparison_minus(b, a, -1, temp_clauses);

    for(int i = 0; i < temp_clauses.size(); i++)
        temp_clauses[i].push_back("-" + helper2);


    for(auto clause : temp_clauses)
        cnf_clauses.push_back(clause);

}
