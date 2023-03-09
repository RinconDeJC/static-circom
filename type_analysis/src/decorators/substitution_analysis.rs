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
type IdSubs = u32;
type IdVar = u32;
type SubsEnvironment = VarEnvironment<IdVar>;
// type SubsMap = HashMap<IdSubs, (IdVar, u32)>;
type VarMap = HashMap<IdVar, HashSet<SubsInfo>>;
#[derive(Clone)]
struct SubsInfo{
    id: IdSubs,
    var_name: String,
    depth: u32,
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
/// between ot the variable goes out of scope before being read.
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
    let mut reports = Vec::new();
    let mut return_set = HashSet::new();
    let mut final_result = HashSet::new();
    let mut found_vars = SubsEnvironment::new();
    let mut non_read = VarMap::new();
    let mut curr_var_id = 0;
    let mut curr_subs_id = 0;
    for param in function_data.get_name_of_params() {
        found_vars.add_variable(param, curr_var_id);
        curr_var_id += 1;
    }
    println!("substitution analysis of function: {}", function_data.get_name());
    analyse_statement(
        body,
        &mut found_vars,
        &mut curr_var_id, 
        &mut non_read,
        &mut curr_subs_id,
        0,
        &mut return_set,
        &mut final_result,
        &mut reports
    );
    println!("Number of useless assignments detected in {}: {} out of {}", function_data.get_name(), final_result.len(), curr_subs_id);
    let mut_body = function_data.get_mut_body();
    curr_subs_id = 0;
    remove_useless_subs(mut_body, &mut curr_subs_id, &final_result, &mut reports);
    println!("------------------");
    reports
}

pub fn template_substitution_analysis(
    template_data: &mut TemplateData
) -> ReportCollection {
    let body = template_data.get_body();
    let mut reports = Vec::new();
    let mut return_set = HashSet::new();
    let mut final_result = HashSet::new();
    let mut found_vars = SubsEnvironment::new();
    let mut non_read = VarMap::new();
    let mut curr_var_id = 0;
    let mut curr_subs_id = 0;
    for param in template_data.get_name_of_params() {
        found_vars.add_variable(param, curr_var_id);
        curr_var_id += 1;
    }
    println!("substitution analysis of template: {}", template_data.get_name());
    analyse_statement(
        body,
        &mut found_vars,
        &mut curr_var_id, 
        &mut non_read,
        &mut curr_subs_id,
        0,
        &mut return_set,
        &mut final_result,
        &mut reports
    );
    println!("Number of useless assignments detected in {}: {} out of {}", template_data.get_name(), final_result.len(), curr_subs_id);
    let mut_body = template_data.get_mut_body();
    curr_subs_id = 0;
    remove_useless_subs(mut_body, &mut curr_subs_id, &final_result, &mut reports);
    println!("------------------");
    reports
}




// ------------------------------------------------
// |       useless substitution detection         |
// ------------------------------------------------

fn analyse_statement(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut u32,
    non_read: &mut VarMap,
    curr_subs_id: &mut IdSubs,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) { 
    match stmt{
        Statement::Block {..}=> {
            println!("block{{");
            analyse_block(stmt, found_vars, curr_var_id,non_read, curr_subs_id, depth + 1, return_set, final_result, reports);
            println!("}}block");
        }
        Statement::IfThenElse {..} =>{
            println!("if else{{");
            analyse_if_else(stmt, found_vars, curr_var_id,non_read, curr_subs_id, depth, return_set, final_result, reports);
            println!("}}if else");
        }
        Statement::While {..} =>{
            println!("while{{");
            analyse_while(stmt, found_vars, curr_var_id,non_read, curr_subs_id, depth, return_set, final_result, reports);
            println!("}}while");
        }
        Statement::Return {..} =>{
            println!("return{{");
            analyse_return(stmt, found_vars, curr_var_id,non_read, curr_subs_id, depth, return_set, final_result, reports);
            println!("}}return");
        }
        Statement::InitializationBlock {..} =>{
            println!("initialization block{{");
            analyse_initialization_block(stmt, found_vars, curr_var_id,non_read, curr_subs_id, depth, return_set, final_result, reports);
            println!("}}initialization block");
        }
        Statement::Declaration {name,..} =>{
            println!("declaration of var {}", name);
            analyse_declaration(stmt, found_vars, curr_var_id,non_read, curr_subs_id, depth, return_set, final_result, reports);
        }
        Statement::Substitution {var, ..} =>{
            println!("assignment of var {}", var);
            analyse_substitution(stmt, found_vars, curr_var_id,non_read, curr_subs_id, depth, return_set, final_result, reports);
        }
        Statement::UnderscoreSubstitution {..} =>{
            analyse_underscore_subs(stmt, found_vars, curr_var_id,non_read, curr_subs_id, depth, return_set, final_result, reports);
        }
        Statement::LogCall {..} =>{
            analyse_log_call(stmt, found_vars, curr_var_id,non_read, curr_subs_id, depth, return_set, final_result, reports);
        }
        Statement::Assert {..} =>{
            analyse_assert(stmt, found_vars, curr_var_id,non_read, curr_subs_id, depth, return_set, final_result, reports);
        }
        _ => {}

    }
}

/// Runs the analysis over every statement in the block, adding a 
/// new block in the Environment. When the block ends, marks
/// every useless substitution due to block ending and variable 
/// disspearing
/// 
fn analyse_block(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut VarMap,
    curr_subs_id: &mut IdSubs,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    use Statement::Block;
    if let Block { stmts,.. } = stmt{
        // add new block
        found_vars.add_variable_block();
        // iterate over statements
        for stmt in stmts.iter() {
            // As we are interested in collecting the union of return sets
            // from each statement, we might aswell just pass the same set
            // to all of them so they get inserted there
            analyse_statement(
                stmt,
                found_vars,
                curr_var_id,
                non_read,
                curr_subs_id,
                depth,
                return_set,
                final_result,
                reports);
        }
        // Mark as useless all the substitutions this block can decide about
        split_useless_subs(return_set, depth, final_result, reports);
        // get outing block and check if there are useless substitutions still here
        let outing_block = found_vars.get_top_block();
        // A substitution of a variable that hasn't been read and whose variable's
        // life is ending can be marked as useless in the result
        for var_id in outing_block.values() {
            if let Option::Some(subs_set) = get_var_content(non_read, *var_id){
                for info in subs_set{
                    // TODO: add warning properly
                    
                    let mut warning = Report::warning(
                        String::from("Useless substitution"),
                        ReportCode::UselessSubstitution
                    );
                    warning.add_primary(
                        info.location.clone(),
                        info.file_id.unwrap(),
                        format!(
                            "{} variable substitution found to be useless",
                            info.var_name
                        )
                    );
                    reports.push(warning);
                    final_result.insert(info.id);
                    println!("DEBUG: assignment with id {} of variable {} asked to be removed", info.id, info.var_name);
                }
            }
        }
    }
    else{
        unreachable!();
    }
}

fn split_useless_subs(
    partial_useless: &mut HashSet<SubsInfo>,
    depth: u32,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    let mut to_remove = Vec::new();
    for info in partial_useless.iter() {
        // If the substitution was made in this block or in an
        // inner block and has been marked as useless, it can be
        // added to the final result and deleted from partial useless
        if info.depth >= depth {
            to_remove.push(info.clone());
            // TODO: add warning properly
            let mut warning = Report::warning(
                String::from("Useless substitution"),
                ReportCode::UselessSubstitution
            );
            warning.add_primary(
                info.location.clone(),
                info.file_id.unwrap(),
                format!(
                    "{} variable substitution found to be useless",
                    info.var_name
                )
            );
            reports.push(warning);
            final_result.insert(info.id);
            println!("DEBUG: assignment with id {} of variable {} asked to be removed", info.id, info.var_name);
        }
        // If the substitution is done in an outer block
        // this block can't yet decide if it is usless, 
        // returning it to an outer block to evaluates this. 
        // So it is kept in partial_useless
    }
    for info in to_remove{
        partial_useless.remove(&info);
    }
}

fn analyse_if_else(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut VarMap,
    curr_subs_id: &mut IdSubs,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    use Statement::IfThenElse;
    if let IfThenElse { cond, if_case, else_case, .. } = stmt {
        let mut read_vars = HashSet::new();
        analyse_expression(cond, &mut read_vars);
        // Process vars in expression
        mark_read_vars(&read_vars, found_vars, non_read);
        // Get the substitutions that the if statement considers useless
        let mut if_useless_set = HashSet::new();
        // Make a copy of non_read_variables before analysing both statements
        let mut non_read_copy = non_read.clone();
        analyse_statement(
            if_case, 
            found_vars, 
            curr_var_id, 
            non_read, 
            curr_subs_id,
            depth, 
            &mut if_useless_set,
            final_result,
            reports
        );
        if let Option::Some(s) = else_case {
            // Clone the non_read map so no collision occur with an
            // execution that this statement shouldn't be able to see
            // No collisions occur with the Environment as they are prepared
            // for this use (assuming there is a block next)
            let mut else_useless_set = HashSet::new();
            analyse_statement(
                s, 
                found_vars, 
                curr_var_id, 
                &mut non_read_copy, 
                curr_subs_id,
                depth,
                &mut else_useless_set,
                final_result,
                reports
            );
            merge_branches(
                non_read,
                &mut if_useless_set,
                &mut non_read_copy, 
                &mut else_useless_set, 
                depth,
                final_result,
                reports
            );
            return_set.extend(if_useless_set);
        }
        else{
            // In case there is an empty else, as if there are no instructions
            // no substitution can be considered useless and the result must be
            // the intersection of the useless substitutions in if and else, the
            // result must be an empty set. 
            // In this case not extending return_set with the result in
            // if_useless_set has that meaning of empty result.
            // Merging branches is still needed to keep coherent information
            // about non read variables
            merge_branches(
                non_read,
                &mut if_useless_set,
                &mut non_read_copy, 
                &mut HashSet::new(), 
                depth,
                final_result,
                reports
            );
            debug_assert!(if_useless_set.is_empty());
        }
    } else {
        unreachable!()
    }
}

fn analyse_while(
    stmt_w: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut VarMap,
    curr_subs_id: &mut IdSubs,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    use Statement::While;
    if let While { cond, stmt, .. } = stmt_w {
        let mut read_vars = HashSet::new();
        analyse_expression(cond, &mut read_vars);
        // Process vars in expression
        mark_read_vars(&read_vars, found_vars, non_read);
        // Get the substitutions that the if statement considers useless
        let mut while_useless_set = HashSet::new();
        // Make a copy of non_read_variables before analysing both statements
        let mut non_read_copy = non_read.clone();
        analyse_statement(
            stmt, 
            found_vars, 
            curr_var_id, 
            non_read, 
            curr_subs_id,
            depth, 
            &mut while_useless_set,
            final_result,
            reports
        );
        // condition will be evaluated again after a possible execution of the
        // loop, so variables read in condition evaluation should be marked
        // as read again
        mark_read_vars(&read_vars, found_vars, non_read);
        
        // This is the equivalent to en empty else case.
        // As the resulting while_useless_set is empty, there is no need
        // to extend return_set
        // Merging branches is still needed to keep coherent information
        // about non read variables
        merge_branches(
            non_read,
            &mut while_useless_set,
            &mut non_read_copy, 
            &mut HashSet::new(), 
            depth,
            final_result,
            reports
        );
        debug_assert!(while_useless_set.is_empty());
        // Repeat the analysis so fixed point is reached
        // Make a copy of non_read_variables before analysing both statements
        let mut non_read_copy = non_read.clone();
        analyse_statement(
            stmt, 
            found_vars, 
            curr_var_id, 
            non_read, 
            curr_subs_id,
            depth, 
            &mut while_useless_set,
            final_result,
            reports
        );        
        // This is the equivalent to en empty else case.
        // As the resulting while_useless_set is empty, there is no need
        // to extend return_set
        // Merging branches is still needed to keep coherent information
        // about non read variables
        merge_branches(
            non_read,
            &mut while_useless_set,
            &mut non_read_copy, 
            &mut HashSet::new(), 
            depth,
            final_result,
            reports
        );
        debug_assert!(while_useless_set.is_empty());

    } else {
        unreachable!()
    }
}

fn analyse_return(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut VarMap,
    curr_subs_id: &mut u32,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    use Statement::Return;
    if let Return { value, .. } = stmt {
        let mut read_vars = HashSet::new();
        analyse_expression(value, &mut read_vars);
        mark_read_vars(&read_vars, found_vars, non_read);
    } else {
        unreachable!()
    }
}

fn analyse_initialization_block(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut VarMap,
    curr_subs_id: &mut IdSubs,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    use Statement::InitializationBlock;
    if let InitializationBlock { initializations, .. } = stmt {
        // add new block
        found_vars.add_variable_block();
        // iterate over statements
        for stmt in initializations.iter() {
            // As we are interested in collecting the union of return sets
            // from each statement, we might aswell just pass the same set
            // to all of them so they get inserted there
            analyse_statement(
                stmt,
                found_vars,
                curr_var_id,
                non_read,
                curr_subs_id,
                depth,
                return_set,
                final_result,
                reports);
        }
        // Mark as useless all the substitutions this block can decide about
        split_useless_subs(return_set, depth, final_result, reports);
    } else {
        unreachable!()
    }
}

fn analyse_declaration(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut VarMap,
    curr_subs_id: &mut u32,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
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

fn analyse_substitution(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut VarMap,
    curr_subs_id: &mut IdSubs,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    use Statement::Substitution;
    if let Substitution { var, access, meta,rhe,.. } = stmt {
        let mut read_vars = HashSet::new();
        analyse_expression(rhe, &mut read_vars);
        // Process vars in expression
        mark_read_vars(&read_vars, found_vars, non_read);
        // Only complete substitutions of variables are considered in this analysis
        if let TypeReduction::Variable = meta.get_type_knowledge().get_reduces_to(){
            if access.len() == 0{
                if let Option::Some(id) = found_vars.get_variable(var){
                    if let Option::Some(subs_set) = 
                            get_var_content_mut(non_read, *id) 
                    {
                        debug_assert!(!subs_set.is_empty());
                        for info in subs_set.iter(){
                            // If the substitution is from an outer block
                            // this node can't decide if it useless in the final
                            // result, so it is added in the set to be returned
                            if info.depth < depth{
                                // TODO: add debug warning properly
                                /*
                                let mut warning = Report::warning(
                                    String::from("Possible useless substitution"),
                                    ReportCode::UselessSubstitution
                                );
                                warning.add_primary(
                                    info.location.clone(),
                                    info.file_id.unwrap(),
                                    format!(
                                        "DEBUG: {} var assignment suspected to be useless",
                                        info.var_name
                                    )
                                );
                                reports.push(warning);
                                */
                                return_set.insert(info.clone());
                            }
                            // If the substitution was made in this block or in an
                            // inner one, it can be marked as useless in the final
                            // result
                            else{
                                // TODO: add warning properly
                                let mut warning = Report::warning(
                                    String::from("Useless substitution"),
                                    ReportCode::UselessSubstitution
                                );
                                warning.add_primary(
                                    info.location.clone(),
                                    info.file_id.unwrap(),
                                    format!(
                                        "{} variable substitution found to be useless",
                                        info.var_name
                                    )
                                );
                                reports.push(warning);
                                final_result.insert(info.id);
                                println!("DEBUG: assignment with id {} of variable {} asked to be removed", info.id, info.var_name);
                            }
                        }
                        // delete every previous non read substitution
                        subs_set.clear();
                    }
                    // Add this substitution to non_read information
                    insert_subs(
                        non_read,
                        *id, 
                        &SubsInfo { 
                            id:*curr_subs_id,
                            var_name:var.clone(),
                            depth:depth,
                            location:meta.location.clone(),
                            file_id:meta.file_id.clone()
                        }
                    );
                    *curr_subs_id += 1;
                }
                else{
                    unreachable!("Found variable not recognized in environment")
                }
            }
        }
        // else, i.e., this is not a full substitution
        //  no checking are performed as this substitutions are
        //  ignored and left in AST as they are
        // Keep in mind they must be ignored aswell during the removal so the id's stay
        // coherent
    } else {
        unreachable!()
    }
}

fn analyse_underscore_subs(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut VarMap,
    curr_subs_id: &mut IdSubs,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    use Statement::UnderscoreSubstitution;
    if let UnderscoreSubstitution { rhe, .. } = stmt {
        let mut read_vars = HashSet::new();
        analyse_expression(rhe, &mut read_vars);
        mark_read_vars(&read_vars, found_vars, non_read);
    } else {
        unreachable!()
    }
}

fn analyse_log_call(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut VarMap,
    curr_subs_id: &mut u32,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    use Statement::LogCall;
    if let LogCall { args, .. } = stmt {
        let mut read_vars = HashSet::new();
        for arg in args.iter() {
            if let LogArgument::LogExp(exp) = arg {
                analyse_expression(exp, &mut read_vars);
            }
        }
        mark_read_vars(&read_vars, found_vars, non_read);
    } else {
        unreachable!()
    }
}

fn analyse_assert(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut VarMap,
    curr_subs_id: &mut IdSubs,
    depth: u32,
    return_set: &mut HashSet<SubsInfo>,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    use Statement::Assert;
    if let Assert { arg, .. } = stmt {
        let mut read_vars = HashSet::new();
        analyse_expression(arg, &mut read_vars);
        mark_read_vars(&read_vars, found_vars, non_read);
    } else {
        unreachable!()
    }
}



/// Given a set with read variables marks unread vars as read
/// taking into account the shadowing features given by the 
/// environment
fn mark_read_vars(
    read_vars: &HashSet<String>,
    found_vars: &SubsEnvironment,
    non_read: &mut VarMap,
){
    for var in read_vars.iter() {
        println!("var in expression found: {}", var);
        if let Option::Some(id) = found_vars.get_variable(var){
            println!("with id: {}", id);
            remove_var(non_read, *id);
        }
        else{
            println!("DEBUG: check {} is not a variable but a declared component or signal", var);
        }
    }
}

/// Returns the variables appearing in the expression inside
/// the HashMap given
fn analyse_expression(
    exp: &Expression,
    read_vars: &mut HashSet<String>,
) {
    match exp{
        Expression::Variable{name,..} => {
            read_vars.insert(name.clone());
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
// |        VarMap manipulation functions         |
// ------------------------------------------------

/// Inserts the pair in both maps. The function assumes that there is
/// no entry for var->subs, so if a useless substitution has been detected
/// it should have been previously detected and removed
fn insert_subs(
    map: &mut VarMap,
    var: IdVar,
    info: &SubsInfo,
) {
    if !map.contains_key(&var) {
        map.insert(var, HashSet::new());
    }
    if let Option::Some(set) = map.get_mut(&var){
        set.insert(info.clone());
    }
    else{
        unreachable!("key has been checked to be present in map")
    }
}

fn contains_var(
    map: &VarMap,
    var: &IdVar,
) -> bool {
    map.contains_key(var)
}

fn contains_subs_of_var(
    map: &VarMap,
    subs_depth: &SubsInfo,
    var: &IdVar,
) -> bool {
    if let Option::Some(set_ref) = map.get(var){
        set_ref.contains(subs_depth)
    }
    else{
        false
    }
    
}

fn get_var_content(
    map: &VarMap,
    var: IdVar,
) -> Option<&HashSet<SubsInfo>> {
    map.get(&var)
}

fn get_var_content_mut(
    map: &mut VarMap,
    var: IdVar,
) -> Option<&mut HashSet<SubsInfo>> {
    map.get_mut(&var)
}

/// Removes all the information related to the variable
fn remove_var(
    map: &mut VarMap,
    var: IdVar,
) {
    map.remove(&var);
}

/// Removes a substitution given the variable where it should be found and the
/// depth at which it was made. If the set ends up empty it is removed
/// 
/// Panics
/// --------
/// If the set of the given variable doesn't contain the pair to be removed
/// or the variable id is not contained in the map as a key
fn remove_subs_of_var (
    map: &mut VarMap,
    var: &IdVar,
    subs_depth: &SubsInfo,
) {
    if let Option::Some(set_ref) = map.get_mut(var) {
        assert!(set_ref.remove(subs_depth));
        if set_ref.is_empty(){
            map.remove(var);
        }
    }
    else{
        assert!(false)
    }
}

/// Gets the resulting VarMap of non read variables 
/// to the right non read variables after the execution of both branches.
/// The result is returned in the first map and second one is from this point 
/// onwards uselss. The criteria is the following:
///     - If a substitution of a variable has been done in this current 
///     block or an outer one, to be still non_read it should be non read in
///     both branches.
///     - If a substitution of a variable has been done in an inner block,
///     it will still be non read.
/// 
/// This function also calculates the useless substitutions as the intersection
/// of both sets of useless substitutions, minus the ones in the intersection
/// whose depth is equal to current_depth. Those are to be added into the final
/// result. The result is returned in the same way as previously mentioned. 
fn merge_branches(
    map: &mut VarMap,
    useless_set: &mut HashSet<SubsInfo>,
    map2: &mut VarMap,
    useless_set2: &mut HashSet<SubsInfo>,
    curr_depth: u32,
    final_result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) {
    // Calculate intersection of useless_sets
    useless_set.retain(|x| useless_set2.contains(x));
    // Now find those whose depth is equal to curr_depth
    // This means that both branches consider this a useless substitution
    // but couldn't asssure it would be in the final result. Now we know it does
    let mut to_remove_from_set = Vec::new();
    for info in useless_set.iter(){
        debug_assert!(info.depth <= curr_depth);
        if info.depth == curr_depth{
            // TODO: add warning properly
            let mut warning = Report::warning(
                String::from("Useless substitution"),
                ReportCode::UselessSubstitution
            );
            warning.add_primary(
                info.location.clone(),
                info.file_id.unwrap(),
                format!(
                    "{} variable substitution found to be useless",
                    info.var_name
                )
            );
            reports.push(warning);
            println!(
                "Detected FINAL useless sub: {} after branching at depth: {}", 
                info.id, 
                info.depth
            );
            to_remove_from_set.push(info.clone());
            // TODO: add warning properly
            let mut warning = Report::warning(
                String::from("Useless substitution"),
                ReportCode::UselessSubstitution
            );
            warning.add_primary(
                info.location.clone(),
                info.file_id.unwrap(),
                format!(
                    "{} variable substitution found to be useless",
                    info.var_name
                )
            );
            reports.push(warning);
            final_result.insert(info.id);
            println!("DEBUG: assignment with id {} of variable {} asked to be removed", info.id, info.var_name);

        }
    }
    for info in to_remove_from_set{
        useless_set.remove(&info);
    }
    

    let mut to_remove: Vec<(IdVar,SubsInfo)> = Vec::new();
    // Find the intersection of substitutions made in this or outer block
    // that are still non read
    for (id_var, set) in map.iter(){
        for info in set.iter(){  
            if info.depth <= curr_depth &&
                !contains_subs_of_var(
                    &map2,
                    info, 
                    id_var)
            {
                to_remove.push((*id_var,info.clone()));
            }
        }
    }
    // Remove all that is to be removed
    for (var, info) in to_remove{
        remove_subs_of_var(map, &var, &info);
    }

    // Find the union of substitutions made in inner blocks
    // that are still non read
    for (id_var, set) in map2{
        for info in set.iter(){
            if info.depth > curr_depth{
                insert_subs(map, *id_var, info);
            }
        }
    }
}

// ------------------------------------------------
// |        useless substitution removal          |
// ------------------------------------------------

fn remove_useless_subs(
    stmt: &mut Statement,
    curr_subs_id: &mut IdSubs, 
    final_result: &HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> bool{
    match stmt{
        Statement::Block {stmts,..}=> {
            stmts.retain_mut(|s| 
                !remove_useless_subs(
                    s, 
                    curr_subs_id, 
                    final_result, 
                    reports)
                );
            false
        }
        Statement::IfThenElse {if_case, else_case,..} =>{
            remove_useless_subs(
                if_case, 
                curr_subs_id, 
                final_result, 
                reports
            );
            if let Option::Some(stmt_else) = else_case{
                remove_useless_subs(
                    stmt_else, 
                    curr_subs_id, 
                    final_result, 
                    reports
                );
            }
            false
        }
        Statement::While {stmt,..} =>{
            remove_useless_subs(
                stmt, 
                curr_subs_id, 
                final_result, 
                reports
            );
            false
        }
        Statement::Substitution {access,var,..} =>{
            // Check if its corresponding id is in final_result
            if access.len() == 0{
                let is_useless = final_result.contains(curr_subs_id);
                *curr_subs_id += 1;
                if is_useless{
                    println!("DEBUG: removing assignment with id {} of var {}", *curr_subs_id-1, var);
                }
                else{
                    println!("DEBUG: assignment with id {} of var {} allowed to be kept", *curr_subs_id-1, var);
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
                    curr_subs_id, 
                    final_result, 
                    reports
                );
            }
            false
        }
        _ => {false}
    }
}