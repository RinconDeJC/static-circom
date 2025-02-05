use program_structure::ast::*;
use program_structure::file_definition::FileLocation;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::function_data::FunctionData;
use program_structure::environment::VarEnvironment;
use program_structure::template_data::TemplateData;
use std::collections::HashSet;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
type IdSubs = usize;
type IdVar = u32;
type SubsEnvironment = VarEnvironment<IdVar>;
type VarMap = HashMap<IdVar, HashSet<SubsInfo>>;
#[derive(Clone)]
struct SubsInfo{
    id: IdSubs,
    var: IdVar,
    var_name: String,
    location: FileLocation,
    file_id: Option<usize>,
    contains_signal: bool,
    is_artificial: bool,
    is_constant: bool,
}
impl Hash for SubsInfo {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl PartialEq for SubsInfo {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for SubsInfo {}


/// Given a function, this analysis checks for useless substitutions
/// in the code and eliminates them.
/// 
/// A subsitution over a variable is considered useless if a valid 
/// substitution is performed on that same variable before it has been read in
/// between or the variable goes out of scope before being read.
/// 
/// A substitution is considered, at the moment, valid, if no access is 
/// performed during the substitution, e.g, 
/// ```
/// x = 0;        // is considered a valid substitution,
/// x[i] = 0;     // this isn't
/// x.field = 0;  // and neither is this.
/// ```
pub fn function_substitution_analysis(
    function_data: &mut FunctionData
) -> ReportCollection {
    let body = function_data.get_body();
    let mut unknown = VarMap::new();
    let mut useless = HashSet::new();
    let mut useful = HashSet::new();
    let mut found_vars = SubsEnvironment::new();
    let mut curr_var_id = 0;
    for param in function_data.get_name_of_params() {
        found_vars.add_variable(param, curr_var_id);
        curr_var_id += 1;
    }
    analyse_statement(
        &mut unknown,
        &mut useful,
        &mut useless,
        &mut found_vars,
        &mut curr_var_id,
        body,
    );
    debug_assert!(unknown.is_empty());
    let mut artificials = useless.clone();
    for info in useless.iter(){
        if !info.is_artificial{
            artificials.remove(info);
        }
    } 
    let mut reports = ReportCollection::new();
    add_warnings(&useless, &mut reports);
    let mut_body = function_data.get_mut_body();
    let mut final_result = HashSet::new();
    for info in useless.iter(){
        final_result.insert(info.id);
    }
    remove_useless_subs(mut_body, &final_result, &mut reports);
    reports
}


/// Given a template, this analysis checks for useless substitutions
/// in the code and eliminates them.
/// 
/// A subsitution over a variable is considered useless if a valid 
/// substitution is performed on that same variable before it has been read in
/// between or the variable goes out of scope before being read.
/// 
/// A substitution is considered, at the moment, valid, if no access is 
/// performed during the substitution, e.g, 
/// ```
/// x = 0;        // is considered a valid substitution,
/// x[i] = 0;     // this isn't
/// x.field = 0;  // and neither is this.
/// ```
pub fn template_substitution_analysis(
    template_data: &mut TemplateData
) -> ReportCollection {
    let body = template_data.get_body();
    let mut unknown = VarMap::new();
    let mut useless = HashSet::new();
    let mut useful = HashSet::new();
    let mut found_vars = SubsEnvironment::new();
    let mut curr_var_id = 0;
    for param in template_data.get_name_of_params() {
        found_vars.add_variable(param, curr_var_id);
        curr_var_id += 1;
    }
    analyse_statement(
        &mut unknown,
        &mut useful,
        &mut useless,
        &mut found_vars,
        &mut curr_var_id,
        body,
    );
    let mut reports = ReportCollection::new();
    debug_assert!(unknown.is_empty());
    let mut artificials = useless.clone();
    for info in useless.iter(){
        if !info.is_artificial{
            artificials.remove(info);
        }
    } 
    add_warnings(&useless, &mut reports);
    let mut_body = template_data.get_mut_body();
    let mut final_result = HashSet::new();
    for info in useless.iter(){
        final_result.insert(info.id);
    }
    remove_useless_subs(mut_body, &final_result, &mut reports);
    reports
}


// ------------------------------------------------
// |               warning handling               |
// ------------------------------------------------
fn add_warnings(
    useless: &HashSet<SubsInfo>,
    reports: &mut ReportCollection
) {
    for info in useless.iter(){
        if info.contains_signal{
            let mut warning = Report::warning(
                String::from("Useless substitution"),
                ReportCode::UselessSubstitution
            );
            warning.add_primary(
                info.location.clone(),
                info.file_id.unwrap(),
                format!(
                    "{} variable substitution is never read and contains signals",
                    info.var_name
                )
            );
            reports.push(warning);
        }
        if !info.is_artificial{
            let mut warning = Report::warning(
                String::from("Useless substitution"),
                ReportCode::UselessSubstitution
            );
            warning.add_primary(
                info.location.clone(),
                info.file_id.unwrap(),
                format!(
                    "{} variable substitution is useless but not artificial{}",
                    info.var_name,
                    if info.is_constant{
                        ". However, it is a constant"
                    }
                    else{
                        ""
                    }
                )
            );
            reports.push(warning);
        }
    }
}


// ------------------------------------------------
// |       useless substitution detection         |
// ------------------------------------------------

fn analyse_statement(
    unknown: &mut VarMap,
    useful: &mut HashSet<SubsInfo>,
    useless: &mut HashSet<SubsInfo>,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    stmt: &Statement, 
) { 
    match stmt{
        Statement::Block {..}=> {
            analyse_block(
                unknown,
                useful,
                useless,
                found_vars,
                curr_var_id,
                stmt,
            );
        }
        Statement::IfThenElse {..} =>{
            analyse_if_else(
                unknown,
                useful,
                useless,
                found_vars,
                curr_var_id,
                stmt,
            );            
        }
        Statement::While {..} =>{
            analyse_while(
                unknown,
                useful,
                useless,
                found_vars,
                curr_var_id,
                stmt,
            );            
        }
        Statement::Return {value,..} =>{
            let mut read_vars = HashSet::new();
            analyse_expression(value, &mut read_vars);
            analyse_reader(
                unknown,
                useful,
                found_vars,
                &read_vars,
            );
        }
        Statement::InitializationBlock {..} =>{
            analyse_initialization_block(
                unknown,
                useful,
                useless,
                found_vars,
                curr_var_id,
                stmt,
            );
        }
        Statement::Declaration {..} =>{
            analyse_declaration(
                found_vars,
                curr_var_id,
                stmt,
            );
        }
        Statement::Substitution {..} =>{
            analyse_assignment(
                unknown,
                useful,
                useless,
                found_vars,
                stmt,
                false,
            );
        }
        Statement::UnderscoreSubstitution {..} =>{

        }
        Statement::ConstraintEquality {lhe, rhe, ..} =>{
            let mut read_vars = HashSet::new();
            analyse_expression(lhe, &mut read_vars);
            analyse_expression(rhe, &mut read_vars);
            analyse_reader(
                unknown,
                useful,
                found_vars,
                &read_vars,
            );
        }
        Statement::LogCall {args, ..} =>{
            let mut read_vars = HashSet::new();
            for arg in args.iter() {
                if let LogArgument::LogExp(exp) = arg {
                    analyse_expression(exp, &mut read_vars);
                }
            }
            analyse_reader(
                unknown,
                useful,
                found_vars,
                &read_vars,
            );
        }
        Statement::Assert {arg, ..} =>{
            let mut read_vars = HashSet::new();
            analyse_expression(arg, &mut read_vars);
            analyse_reader(
                unknown,
                useful,
                found_vars,
                &read_vars,
            );
        }
        _ => {unreachable!();}

    }
}

fn analyse_reader(
    unknown: &mut VarMap,
    useful: &mut HashSet<SubsInfo>,
    found_vars: &mut SubsEnvironment,
    read_vars: &HashSet<String>,
) {
    // NewUseful = {(x,id) \in Unknown : x \in read_vars}
    // Unknown = Unknown \ NewUseful
    // Useful = Useful \cup NewUseful
    for var_name in read_vars.iter() {
        let op_var_id = found_vars.get_variable(var_name);
        if let Option::Some(var_id) = op_var_id{
            if let Option::Some(info_set) = unknown.remove(var_id){
                useful.extend(info_set);
            }
        }
        else{
            unreachable!();
        }
    }
}

fn analyse_assignment(
    unknown: &mut VarMap,
    useful: &mut HashSet<SubsInfo>,
    useless: &mut HashSet<SubsInfo>,
    found_vars: &mut SubsEnvironment,
    stmt: &Statement,
    is_constant: bool,
) {
    use Statement::Substitution;
    if let Substitution { var, access, meta, rhe,is_artificial,.. } = stmt {
        // NewUseful = {(x,id) \in Unknown : x \in rhe}
        // Unknown = Unknown \ NewUseful
        // Useful = Useful \cup NewUseful
        let mut read_vars = HashSet::new();
        analyse_expression(rhe, &mut read_vars);
        for acc_exp in access.iter(){
            if let Access::ArrayAccess(index) = acc_exp{
                analyse_expression(index, &mut read_vars);
            }
        }
        analyse_reader(unknown, useful, found_vars, &read_vars);
        if let TypeReduction::Variable = meta.get_type_knowledge().get_reduces_to(){
            if access.len() == 0 {
                if let Option::Some(var_id) = found_vars.get_variable(var){
                    // NewUseless = {(y, id) \in Unknown}
                    // Unknown = Unknown \ NewUseless
                    // Useless = Useless \cup NewUseless
                    if let Option::Some(info_set) = unknown.remove(var_id){
                        useless.extend(info_set);
                    }

                    let assignment_info = SubsInfo { 
                        id:meta.elem_id,
                        var:*var_id,
                        var_name:var.clone(),
                        location:meta.location.clone(),
                        file_id:meta.file_id.clone(),
                        contains_signal: expression_contains_signals(rhe),
                        is_artificial: *is_artificial, 
                        is_constant: is_constant,
                    };
                    let mut has_appeared = useless.contains(&assignment_info);
                    has_appeared = has_appeared || useful.contains(&assignment_info);
                    if let Option::Some(info_set) = unknown.get(var_id) {
                        has_appeared = has_appeared || info_set.contains(&assignment_info);
                    }
                    // if (y, id_node) \notin Unknown \cup Useless \cup Usefull
                    if !has_appeared {
                        // Unknown = Unknown \cup {(y, id_node)}
                        if let Option::Some(info_set) = unknown.get_mut(var_id) {
                            info_set.insert(assignment_info);
                        }
                        else{
                            let mut new_set = HashSet::new();
                            new_set.insert(assignment_info);
                            unknown.insert(*var_id, new_set);
                        }
                    }
                }
                else{
                    unreachable!();
                }
            }
        }  
    }
    else{
        unreachable!();
    }
}

fn analyse_block(
    unknown: &mut VarMap,
    useful: &mut HashSet<SubsInfo>,
    useless: &mut HashSet<SubsInfo>,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    stmt: &Statement,
) {
    use Statement::Block;
    if let Block { stmts,.. } = stmt{
        // add new block
        found_vars.add_variable_block();
        // iterate over statements
        for stmt in stmts.iter() {
            analyse_statement(
                unknown,
                useful,
                useless,
                found_vars,
                curr_var_id,
                stmt);
        }
        let outing_block = found_vars.get_top_block();
        // NewUseless = {(x, id) \in Unknown : x \in OutingVariables}
        // Unknown = Unknown \ NewUseless
        // Useless = Useless \cup NewUseless
        for var_id in outing_block.values() {
            if let Option::Some(info_set) = unknown.remove(var_id){
                useless.extend(info_set);
            }
        }
        // Remove outing block
        found_vars.remove_variable_block();
    }
    else{
        unreachable!();
    }
}

fn merge_branches(
    unknown1: &mut VarMap,
    unknown2: VarMap,
    useful1: &mut HashSet<SubsInfo>,
    useful2:  HashSet<SubsInfo>,
    useless1: &mut HashSet<SubsInfo>,
    useless2: HashSet<SubsInfo>,
) {
    // Useful = Useful1 \cup Useful2, 
    //   but we put into Useful1 to avoid creating more sets
    useful1.extend(useful2);
    // Unknown = Unknown1 \cup Unknown2,
    for (id_var, set_info2) in unknown2 {
        if let Option::Some(set_info1) = unknown1.get_mut(&id_var) {
            set_info1.extend(set_info2);
        }
    }
    // Useless = Useless1 \cup Useless2
    useless1.extend(useless2);
    // Unknown = Unknown \ Useful
    // Useless = Useless \ Useful
    for info in useful1.iter() {
        if let Option::Some(set_info) = unknown1.get_mut(&info.var) {
            set_info.remove(&info);
            if set_info.is_empty() {
                unknown1.remove(&info.var);
            }
        }
        useless1.remove(&info);
    }
    // Useless = Useless \ Unknown
    for (_, set_info) in unknown1.iter() {
        for info in set_info.iter() {
            useless1.remove(&info);
        }
    }
}

fn analyse_if_else(
    unknown: &mut VarMap,
    useful: &mut HashSet<SubsInfo>,
    useless: &mut HashSet<SubsInfo>,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    stmt: &Statement,
) {
    use Statement::IfThenElse;
    if let IfThenElse { cond, if_case, else_case, .. } = stmt {
        let mut read_vars = HashSet::new();
        analyse_expression(cond, &mut read_vars);
        analyse_reader(unknown, useful, found_vars, &read_vars);

        // Make copies of sets
        let mut unknown_else = unknown.clone();
        let mut useful_else = useful.clone();
        let mut useless_else = useless.clone();
        analyse_statement(
            unknown, 
            useful, 
            useless, 
            found_vars, 
            curr_var_id,
            if_case);
        if let Option::Some(else_stmt) = else_case {
            analyse_statement(
                &mut unknown_else, 
                &mut useful_else, 
                &mut useless_else, 
                found_vars, 
                curr_var_id,
                else_stmt);
        }
        merge_branches(
            unknown, 
            unknown_else, 
            useful, 
            useful_else, 
            useless, 
            useless_else);
    }
    else{
        unreachable!();
    }

}

fn analyse_while(
    unknown: &mut VarMap,
    useful: &mut HashSet<SubsInfo>,
    useless: &mut HashSet<SubsInfo>,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    stmt_w: &Statement,
) {
    use Statement::While;
    if let While { cond, stmt, .. } = stmt_w {
        let mut read_vars = HashSet::new();
        // 0 iterations
        analyse_expression(cond, &mut read_vars);
        analyse_reader(unknown, useful, found_vars, &read_vars);

        // Make copies of sets
        let mut unknown_1 = unknown.clone();
        let mut useful_1 = useful.clone();
        let mut useless_1 = useless.clone();
        // 1 iteration
        analyse_statement(
            &mut unknown_1, 
            &mut useful_1, 
            &mut useless_1, 
            found_vars, 
            curr_var_id, 
            stmt);
        analyse_reader(&mut unknown_1, &mut useful_1, found_vars, &read_vars);    
        
        // Make copies of sets
        let mut unknown_2 = unknown_1.clone();
        let mut useful_2 = useful_1.clone();
        let mut useless_2 = useless_1.clone();
        // 2 iterations
        analyse_statement(
            &mut unknown_2, 
            &mut useful_2, 
            &mut useless_2, 
            found_vars, 
            curr_var_id,
            stmt);
        analyse_reader(&mut unknown_2, &mut useful_2, found_vars, &read_vars);    
        
        // merge 0 and 1 iterations
        merge_branches(
            unknown, 
            unknown_1, 
            useful, 
             useful_1, 
            useless, 
            useless_1);
        // merge 0, 1 and 2 iterations
        merge_branches(
            unknown, 
            unknown_2, 
            useful, 
             useful_2, 
            useless, 
            useless_2);
    }
    else{
        unreachable!();
    }

}

fn analyse_initialization_block(
    unknown: &mut VarMap,
    useful: &mut HashSet<SubsInfo>,
    useless: &mut HashSet<SubsInfo>,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar, 
    stmt_i: &Statement,
) {
    use Statement::{InitializationBlock, Declaration, Substitution};
    if let InitializationBlock { initializations, .. } = stmt_i {
        // iterate over statements
        let mut constants = HashSet::new();
        for s in initializations.iter() {
            if let Declaration { name, is_constant, .. } = s {
                if *is_constant {
                    constants.insert(name.clone());
                }
            }
        }
        for stmt in initializations.iter() {
            match stmt {
                Declaration {..} => {
                    analyse_declaration(found_vars, curr_var_id, stmt);
                },
                Substitution {var, ..} => {
                    analyse_assignment(
                        unknown, 
                        useful, 
                        useless, 
                        found_vars, 
                        stmt, 
                        constants.contains(var));
                },
                _ => {unreachable!();}

            }
        }
    } else {
        unreachable!()
    }
}

fn analyse_declaration(
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    stmt: &Statement,
) {
    use Statement::Declaration;
    if let Declaration { name, xtype, .. } = stmt {
        if let VariableType::Var = xtype{
            found_vars.add_variable(name, *curr_var_id);
            *curr_var_id += 1;
        }
    } else {
        unreachable!()
    }
}


/// Returns the variables appearing in the expression inside
/// the HashMap given
fn analyse_expression(
    exp: &Expression,
    read_vars: &mut HashSet<String>,
) {
    match exp{
        Expression::Variable{name,meta,access,..} => {
            if let TypeReduction::Variable = 
                meta.get_type_knowledge().get_reduces_to()
            {
                read_vars.insert(name.clone());
            }
            for acc_exp in access.iter(){
                if let Access::ArrayAccess(index) = acc_exp{
                    analyse_expression(index, read_vars);
                }
            }
        },
        Expression::InfixOp { lhe, rhe, ..} => {
            analyse_expression(lhe, read_vars);
            analyse_expression(rhe, read_vars);
        },
        Expression::PrefixOp{rhe,..} => {
            analyse_expression(rhe, read_vars);
        },
        Expression::InlineSwitchOp { cond, if_true, if_false,.. }=> {
            analyse_expression(cond, read_vars);
            analyse_expression(if_true, read_vars);
            analyse_expression(if_false, read_vars);
        },
        Expression::ParallelOp{rhe,..} => {
            analyse_expression(rhe, read_vars);
        },
        Expression::Call{args,..} => {
            for arg in args.iter() {
                analyse_expression(arg, read_vars);
            }            
        },
        Expression::AnonymousComp {params, signals,.. }=> {
            for param in params.iter(){
                analyse_expression(param, read_vars);
            }
            for signal in signals.iter(){
                analyse_expression(signal, read_vars);
            }
        },
        Expression::ArrayInLine{values,..} => {
            for value in values.iter() {
                analyse_expression(value, read_vars);
            }            
        },
        Expression::Tuple{values,..} => {
            for value in values.iter() {
                analyse_expression(value, read_vars);
            }            
        },
        Expression::UniformArray{value,dimension,..} => {
            analyse_expression(value, read_vars);
            analyse_expression(dimension, read_vars);          
        },
        _ => {}
    }
}

/// Returns the variables appearing in the expression inside
/// the HashMap given
fn expression_contains_signals(
    exp: &Expression,
) -> bool {
    match exp{
        Expression::Variable{meta,..} => {
            if let TypeReduction::Signal = 
                meta.get_type_knowledge().get_reduces_to()
            {
                return true;
            }
            return false;
        },
        Expression::InfixOp { lhe, rhe, ..} => {
            expression_contains_signals(lhe)
            ||
            expression_contains_signals(rhe)
        },
        Expression::PrefixOp{rhe,..} => {
            expression_contains_signals(rhe)
        },
        Expression::InlineSwitchOp { cond, if_true, if_false,.. }=> {
            expression_contains_signals(cond)
            ||
            expression_contains_signals(if_true)
            ||
            expression_contains_signals(if_false)
        },
        Expression::ParallelOp{rhe,..} => {
            expression_contains_signals(rhe)
        },
        Expression::Call{args,..} => {
            for arg in args.iter() {
                if expression_contains_signals(arg) {
                    return true;
                }
            }
            return false;        
        },
        Expression::AnonymousComp {params, signals,.. }=> {
            for param in params.iter(){
                if expression_contains_signals(param) {
                    return true;
                }
            }
            for signal in signals.iter(){
                if expression_contains_signals(signal) {
                    return true;
                }
            }
            return false;
        },
        Expression::ArrayInLine{values,..} => {
            for value in values.iter() {
                if expression_contains_signals(value){
                    return true;
                }
            }
            return false;
        },
        Expression::Tuple{values,..} => {
            for value in values.iter() {
                if expression_contains_signals(value) {
                    return true;
                }
            }
            return false;
        },
        Expression::UniformArray{value,dimension,..} => {
            expression_contains_signals(value)
            ||
            expression_contains_signals(dimension)      
        },
        _ => {false}
    }
}

// ------------------------------------------------
// |        useless substitution removal          |
// ------------------------------------------------

fn remove_useless_subs(
    stmt: &mut Statement,
    final_result: &HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> bool{
    match stmt{
        Statement::Block {stmts,..}=> {
            stmts.retain_mut(|s| 
                !remove_useless_subs(
                    s, 
                    final_result, 
                    reports)
                );
            false
        }
        Statement::IfThenElse {if_case, else_case,..} =>{
            remove_useless_subs(
                if_case, 
                final_result, 
                reports
            );
            if let Option::Some(stmt_else) = else_case{
                remove_useless_subs(
                    stmt_else, 
                    final_result, 
                    reports
                );
            }
            false
        }
        Statement::While {stmt,..} =>{
            remove_useless_subs(
                stmt, 
                final_result, 
                reports
            );
            false
        }
        Statement::Substitution {access,meta,..} =>{
            // Check if its corresponding id is in final_result
            if access.len() == 0{
                final_result.contains(&meta.elem_id)
            }
            else{
                false
            }
        }          
        Statement::InitializationBlock {initializations,.. } =>{
            initializations.retain_mut(|s| 
                !remove_useless_subs(
                    s, 
                    final_result, 
                    reports)
                );
            false
        }
        _ => {false}
    }
}

