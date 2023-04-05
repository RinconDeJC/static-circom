use program_structure::ast::*;
use program_structure::file_definition::FileLocation;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition;
use program_structure::function_data::FunctionData;
use program_structure::environment::VarEnvironment;
use program_structure::template_data::TemplateData;
use std::collections::HashSet;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
type IdSubs = usize;
type IdVar = u32;
type SubsEnvironment = VarEnvironment<IdVar>;
// type SubsMap = HashMap<IdSubs, (IdVar, u32)>;
type VarMap = HashMap<IdVar, HashSet<SubsInfo>>;
#[derive(Clone)]
struct SubsInfo{
    id: IdSubs,
    var: IdVar,
    var_name: String,
    location: FileLocation,
    file_id: Option<usize>,
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
// NOTA: El tipo al que se reduce cada variable ya está apuntado en el Meta de 
// cada variable

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
    println!("substitution analysis of function: {}", function_data.get_name());
    analyse_statement(
        &mut unknown,
        &mut useful,
        &mut useless,
        &mut found_vars,
        &mut curr_var_id,
        body,
    );
    debug_assert!(unknown.is_empty());
    println!("Number of useless assignments detected in function {}: {}", function_data.get_name(), useless.len());
    println!("Number of useful assignments detected in function {}: {}", function_data.get_name(), useful.len());
    println!("Number of unknown assignments detected in function {}: {}", function_data.get_name(), unknown.len());
    let mut reports = ReportCollection::new();
    let mut_body = function_data.get_mut_body();
    let mut tmp_reports = ReportCollection::new();
    let mut final_result = HashSet::new();
    for info in useless.iter(){
        final_result.insert(info.id);
    }
    remove_useless_subs(mut_body, &final_result, &mut tmp_reports);
    println!("------------------");
    // TODO: add proper warnings
    reports
}

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
    println!("substitution analysis of template: {}", template_data.get_name());
    analyse_statement(
        &mut unknown,
        &mut useful,
        &mut useless,
        &mut found_vars,
        &mut curr_var_id,
        body,
    );
    debug_assert!(unknown.is_empty());
    println!("Number of useless assignments detected in template {}: {}", template_data.get_name(), useless.len());
    println!("Number of useful assignments detected in template {}: {}", template_data.get_name(), useful.len());
    println!("Number of unknown assignments detected in template {}: {}", template_data.get_name(), unknown.len());
    let mut reports = ReportCollection::new();
    let mut_body = template_data.get_mut_body();
    let mut tmp_reports = ReportCollection::new();
    let mut final_result = HashSet::new();
    for info in useless.iter(){
        final_result.insert(info.id);
    }
    remove_useless_subs(mut_body, &final_result, &mut tmp_reports);
    println!("------------------");
    // TODO: add proper warnings
    reports
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
            // println!("block{{");
            analyse_block(
                unknown,
                useful,
                useless,
                found_vars,
                curr_var_id,
                stmt,
            );
            // println!("}}block");
        }
        Statement::IfThenElse {..} =>{
            // println!("if else{{");
            analyse_if_else(
                unknown,
                useful,
                useless,
                found_vars,
                curr_var_id,
                stmt,
            );            
            // println!("}}if else");
        }
        Statement::While {..} =>{
            // println!("while{{");
            analyse_while(
                unknown,
                useful,
                useless,
                found_vars,
                curr_var_id,
                stmt,
            );            
            // println!("}}while");
        }
        Statement::Return {value,..} =>{
            // println!("return{{");
            let mut read_vars = HashSet::new();
            analyse_expression(value, &mut read_vars);
            analyse_reader(
                unknown,
                useful,
                found_vars,
                &read_vars,
            );
            // println!("}}return");
        }
        Statement::InitializationBlock {..} =>{
            // println!("initialization block{{");
            analyse_initialization_block(
                unknown,
                useful,
                useless,
                found_vars,
                curr_var_id,
                stmt,
            );
            // println!("}}initialization block");
        }
        Statement::Declaration {name,..} =>{
            // println!("declaration of var {}", name);
            analyse_declaration(
                found_vars,
                curr_var_id,
                stmt,
            );
        }
        Statement::Substitution {var, meta, ..} =>{
            // println!("assignment with id {} of var {}", meta.elem_id, var);
            analyse_assignment(
                unknown,
                useful,
                useless,
                found_vars,
                stmt,
            );
        }
        Statement::UnderscoreSubstitution {..} =>{
            analyse_underscore_subs(
                unknown,
                useful,
                useless,
                found_vars,
                curr_var_id,
                stmt,
            );
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
) {
    use Statement::Substitution;
    if let Substitution { var, access, meta, rhe,.. } = stmt {
        // NewUseful = {(x,id) \in Unknown : x \in rhe}
        // Unknown = Unknown \ NewUseful
        // Useful = Useful \cup NewUseful
        let mut rhe_vars = HashSet::new();
        analyse_expression(rhe, &mut rhe_vars);
        analyse_reader(unknown, useful, found_vars, &rhe_vars);

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
                        file_id:meta.file_id.clone()
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
    unknown2: & VarMap,
    useful1: &mut HashSet<SubsInfo>,
    useful2: & HashSet<SubsInfo>,
    useless1: &mut HashSet<SubsInfo>,
    useless2: & HashSet<SubsInfo>,
) {
    // Useful = Useful1 \cup Useful2, 
    //   but we put into Useful1 to avoid creating more sets
    useful1.extend(useful2.iter().cloned());
    // Unknown = Unknown1 \cup Unknown2,
    for (id_var, set_info2) in unknown2.iter() {
        if let Option::Some(set_info1) = unknown1.get_mut(id_var) {
            set_info1.extend(set_info2.iter().cloned());
        }
    }
    // Useless = Useless1 \cup Useless2
    useless1.extend(useless2.iter().cloned());
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
            &unknown_else, 
            useful, 
            & useful_else, 
            useless, 
            &useless_else);
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
            &unknown_1, 
            useful, 
            & useful_1, 
            useless, 
            &useless_1);
        // merge 0, 1 and 2 iterations
        merge_branches(
            unknown, 
            &unknown_2, 
            useful, 
            & useful_2, 
            useless, 
            &useless_2);
    }
    else{
        unreachable!();
    }

}
// Sample of warning addition, temporary
// let mut warning = Report::warning(
//     String::from("Useless substitution"),
//     ReportCode::UselessSubstitution
// );
// warning.add_primary(
//     info.location.clone(),
//     info.file_id.unwrap(),
//     format!(
//         "{} variable substitution found to be useless",
//         info.var_name
//     )
// );
// reports.push(warning);
// final_result.insert(info.id);

fn analyse_initialization_block(
    unknown: &mut VarMap,
    useful: &mut HashSet<SubsInfo>,
    useless: &mut HashSet<SubsInfo>,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar, 
    stmt_i: &Statement,
) {
    use Statement::InitializationBlock;
    if let InitializationBlock { initializations, .. } = stmt_i {
        // iterate over statements
        for stmt in initializations.iter() {
            analyse_statement(
                unknown, 
                useful, 
                useless, 
                found_vars, 
                curr_var_id, 
                stmt);
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
            // println!("DEBUG: Var {} -> id {}", name, *curr_var_id);
            *curr_var_id += 1;
        }
    } else {
        unreachable!()
    }
}

fn analyse_underscore_subs(
    unknown: &mut VarMap,
    useful: &mut HashSet<SubsInfo>,
    useless: &mut HashSet<SubsInfo>,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    stmt: &Statement,
) {
    // DUDA: preguntar para qué sirven y si hay que tenerlas en cuenta 
    use Statement::UnderscoreSubstitution;
    if let UnderscoreSubstitution { rhe, .. } = stmt {
        //let mut read_vars = HashSet::new();
        //analyse_expression(rhe, &mut read_vars);
        //mark_read_vars(&read_vars, found_vars, non_read);
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
            // DUDA: signals no debería tenerse en cuenta porque estamos seguros de que 
            // aqui no hay señales?
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
        Statement::Substitution {access,var,meta,..} =>{
            // Check if its corresponding id is in final_result
            if access.len() == 0{
                let is_useless = final_result.contains(&meta.elem_id);
                let type_reduction = meta.get_type_knowledge().get_reduces_to();
                if is_useless{
                    match type_reduction {
                        TypeReduction::Variable =>{
                            println!("DEBUG: removing assignment with id {} of var {}", meta.elem_id, var);
                        
                        },
                        _ => {debug_assert!(false);}
                    }
                }
                else{
                    let type_string; 
                    match type_reduction {
                        TypeReduction::Variable =>{
                            type_string = "var";
                        },
                        TypeReduction::Component =>{
                            type_string = "component";
                        },
                        TypeReduction::Signal =>{
                            type_string = "signal";
                        },
                        TypeReduction::Tag =>{
                            type_string = "tag";
                        }
                    }
                    println!("DEBUG: assignment with id {} of {} {} allowed to be kept", meta.elem_id, type_string, var);
                }
                is_useless
            }
            else{
                false
            }
        }          
        Statement::InitializationBlock {initializations,.. } =>{
            for ini in initializations{
                remove_useless_subs(
                    ini, 
                    final_result, 
                    reports
                );
            }
            false
        }
        _ => {false}
    }
}