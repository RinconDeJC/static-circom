use program_structure::ast::*;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition;
use program_structure::function_data::FunctionData;
use program_structure::environment::VarEnvironment;
use std::collections::HashSet;
use std::collections::HashMap;
type IdSubs = u32;
type IdVar = u32;
type SubsEnvironment = VarEnvironment<IdVar>;
type SubsMap = HashMap<IdSubs, (IdVar, u32)>;
type VarMap = HashMap<IdVar, HashSet<(IdSubs, u32)>>;
// NOTA: El tipo al que se reduce cada variable ya está apuntado en el Meta de 
// cada variable
#[derive(Clone)]
struct DoubleIndexedMap{
    subs_to_var : SubsMap,
    var_to_subs : VarMap,
}
/// Given a function, this analysis checks for useless substitutions
/// in the code and eliminates them.
/// 
/// A subsitution over a variable is considered useless if a valid 
/// substitution is performed on that same variable before it has been read in
/// between.
/// 
/// A substitution is considered, at the moment, valid if no access is 
/// performed during the substitution, e.g, 
/// ```
/// x = 0;        // is considered a valid substitution,
/// x[i] = 0;     // this isn't
/// x.field = 0;  // and neither is this.
/// ```
pub fn function_substitution_analysis(
    function_data: &FunctionData
) -> ReportCollection {
    let body = function_data.get_body();
    let mut reports = Vec::new();
    let mut result = HashSet::new();
    let mut found_vars = SubsEnvironment::new();
    let mut non_read = DoubleIndexedMap{
                            subs_to_var: SubsMap::new(), 
                            var_to_subs: VarMap::new()
                        };
    let mut curr_var_id = 0;
    for param in function_data.get_name_of_params() {
        // TODO decidir cómo determinar el id
        found_vars.add_variable(param, 1);
    }
    analyse_statement(
        body,
        &mut found_vars,
        &mut curr_var_id, 
        &mut non_read, 
        0,
        &mut result,
        &mut reports
    );
    reports
}

fn analyse_statement(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut u32,
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>>  { 
    match stmt{
        Statement::Block {..}=> {
            analyse_block(stmt, found_vars, curr_var_id,non_read, depth, result, reports)
        }
        Statement::IfThenElse {..} =>{
            analyse_if_else(stmt, found_vars, curr_var_id,non_read, depth, result, reports)
        }
        Statement::While {..} =>{
            analyse_while(stmt, found_vars, curr_var_id,non_read, depth, result, reports)
        }
        Statement::Return {..} =>{
            analyse_return(stmt, found_vars, curr_var_id,non_read, depth, result, reports)
        }
        Statement::InitializationBlock {..} =>{
            analyse_initialization_block(stmt, found_vars, curr_var_id,non_read, depth, result, reports)
        }
        Statement::Declaration {..} =>{
            analyse_declaration(stmt, found_vars, curr_var_id,non_read, depth, result, reports)
        }
        Statement::Substitution {..} =>{
            analyse_substitution(stmt, found_vars, curr_var_id,non_read, depth, result, reports)
        }
        Statement::MultSubstitution {..} =>{
            analyse_mult_substitution(stmt, found_vars, curr_var_id,non_read, depth, result, reports)
        }
        Statement::LogCall {..} =>{
            analyse_log_call(stmt, found_vars, curr_var_id,non_read, depth, result, reports)
        }
        Statement::Assert {..} =>{
            analyse_assert(stmt, found_vars, curr_var_id,non_read, depth, result, reports)
        }
        _ => {Option::None}

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
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>> {
    use Statement::Block;
    if let Block { stmts,.. } = stmt{
        // add new block
        found_vars.add_variable_block();
        let mut useless_subs: HashSet<(IdSubs, u32)> = HashSet::new();
        // iterate over statements
        for stmt in stmts.iter() {
            if let Option::Some(subs_set) = 
                analyse_statement(
                    stmt,
                    found_vars,
                    curr_var_id,
                    non_read,
                    depth,
                    result,
                    reports
                ){
                    useless_subs.extend(&subs_set);
                }
        }
        // Mark as useless all the substitutions this block can decide about
        let return_set = split_useless_subs(&useless_subs, depth, result);
        // get outing block and check if there are useless substitutions still here
        let outing_block = found_vars.get_top_block();
        // A substitution of a variable that hasn't been read and whose variable's
        // life is ending can be marked as useless in the result
        for var_id in outing_block.values() {
            if let Option::Some(subs_set) = get_var_content(non_read, *var_id){
                for (subs_id, _) in subs_set{
                    result.insert(*subs_id);
                }
            }
        }
        Option::Some(return_set)
    }
    else{
        unreachable!();
    }
}

fn split_useless_subs(
    useless_subs: &HashSet<(IdSubs, u32)>,
    depth: u32,
    result: &mut HashSet<IdSubs>,
) -> HashSet<(IdSubs, u32)> {
    let mut return_set: HashSet<(IdSubs, u32)> = HashSet::new();
    for (id, d) in useless_subs.iter() {
        // If the substitution was made in this block or in an
        // inner block and has been marked as usless, it can be
        // added to the final result
        if *d >= depth {
            result.insert(*id);
        }
        // If the substitution is done in an outer block
        // this block can't yet decide if it is usless, 
        // so it will be returned to an outer block
        // evaluates this
        else{
            return_set.insert((*id, *d));
        }
    }
    return return_set;
}

fn analyse_if_else(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>> {
    use Statement::IfThenElse;
    if let IfThenElse { cond, if_case, else_case, .. } = stmt {
        let mut read_vars = HashSet::new();
        analyse_expression(cond, &mut read_vars);
        // Process vars in expression
        mark_read_vars(&read_vars, found_vars, non_read);
        // Get the substitutions that the if statement considers useless
        let mut if_useless_set =  
            analyse_statement(
                if_case, 
                found_vars, 
                curr_var_id, 
                non_read, 
                depth, 
                result, 
                reports
            );
        if let Option::Some(s) = else_case {
            // Clone the non_read map so no collision occur with an
            // execution that this statement shouldn't be able to see
            // No collisions occur with the Environment as they are prepared
            // for this use (assuming there is a block next)
            let mut non_read_copy = non_read.clone();
            let else_usless_set = 
            analyse_statement(
                s, 
                found_vars, 
                curr_var_id, 
                &mut non_read_copy, 
                depth, 
                result, 
                reports
            );
            if let Option::Some(mut if_set) = if_useless_set{
                let mut wrapper = Option::Some(&mut if_set);
                merge_branches(
                    non_read,
                    &mut wrapper,
                    non_read_copy, 
                    else_usless_set, 
                    depth
                );
                if let Option::Some(_) = wrapper{
                    Option::Some(if_set)
                }
                else{
                    Option::None
                }  
            }
            else{
                merge_branches(
                    non_read,
                    &mut Option::None,
                    non_read_copy, 
                    else_usless_set, 
                    depth
                );
                Option::None
            }
            
            // DUDA: Si antes he cogido una referencia mutable al 
            // al elemento que está dentro del Option, estoy devolviendo bien
            // este option con el HashSet de dentro cambiado como haya hecho
            // merge_branches?
        }
        else{
            // In case there is an empty else, as if there are no instructions
            // no substitution can be considered useless and the result must be
            // the intersection of the useless substitutions in if and else, the
            // result must be an empty set. 
            // In this case Option::None represents that
            Option::None
        }
    } else {
        unreachable!()
    }
}

fn analyse_while(
    stmt_w: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>> {
    use Statement::While;
    if let While { cond, stmt, .. } = stmt_w {
        // TODO: same approach as an if else with an empty else
        panic!("Not implemented")
    } else {
        unreachable!()
    }
}

fn analyse_return(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>> {
    use Statement::Return;
    if let Return { value, .. } = stmt {
        let mut read_vars = HashSet::new();
        analyse_expression(value, &mut read_vars);
        mark_read_vars(&read_vars, found_vars, non_read);
        Option::None
    } else {
        unreachable!()
    }
}

 // DUDA: Este hace falta?
fn analyse_initialization_block(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>> {
    use Statement::InitializationBlock;
    if let InitializationBlock { initializations, .. } = stmt {
        // TODO
        panic!("Not implemented")
    } else {
        unreachable!()
    }
}

fn analyse_declaration(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>> {
    use Statement::Declaration;
    if let Declaration { name, .. } = stmt {
        found_vars.add_variable(name, *curr_var_id);
        *curr_var_id += 1;
        Option::None
    } else {
        unreachable!()
    }
}

fn analyse_substitution(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>> {
    use Statement::Substitution;
    if let Substitution { var, access, .. } = stmt {
        // DUDA: para comprobar si no hay accesos basta ver que 
        //  access tiene longitud 0?
        
        // Only complete substitutions are considered in this analysis
        if access.len() == 0 {
            if let Option::Some(id) = found_vars.get_variable(var){
                if let Option::Some(subs_set) = 
                        get_var_content(non_read, *id) 
                {
                    debug_assert!(!subs_set.is_empty());
                    let mut useless_set: HashSet<(IdSubs, u32)> = HashSet::new();
                    for (subs_id, d) in subs_set{
                        // If the substitution is from an outer block
                        // this node can't decide if it useless in the final
                        // result, so it is added in the set to be returned
                        if *d < depth{
                            useless_set.insert((*subs_id,*d));
                        }
                        // If the substitution was made in this block or and
                        // inner one, it can be marked as useless in the result
                        else{
                            result.insert(*subs_id);
                        }
                    }
                    Option::Some(useless_set)
                }
                else{
                    Option::None
                }
            }
            else{
                unreachable!("Found variable not recognized in environment")
            }
        }
        else{
            Option::None
        }
    } else {
        unreachable!()
    }
}

 // DUDA: Este hace falta?
 fn analyse_mult_substitution(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>> {
    use Statement::InitializationBlock;
    if let InitializationBlock { initializations, .. } = stmt {
        // TODO
        panic!("Not implemented")
    } else {
        unreachable!()
    }
}

fn analyse_log_call(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>> {
    use Statement::LogCall;
    if let LogCall { args, .. } = stmt {
        let mut read_vars = HashSet::new();
        for arg in args.iter() {
            if let LogArgument::LogExp(exp) = arg {
                analyse_expression(exp, &mut read_vars);
            }
        }
        mark_read_vars(&read_vars, found_vars, non_read);
        Option::None
    } else {
        unreachable!()
    }
}

fn analyse_assert(
    stmt: &Statement,
    found_vars: &mut SubsEnvironment,
    curr_var_id: &mut IdVar,
    non_read: &mut DoubleIndexedMap,
    depth: u32,
    result: &mut HashSet<IdSubs>,
    reports: &mut ReportCollection,
) -> Option<HashSet<(IdSubs, u32)>> {
    use Statement::Assert;
    if let Assert { arg, .. } = stmt {
        let mut read_vars = HashSet::new();
        analyse_expression(arg, &mut read_vars);
        mark_read_vars(&read_vars, found_vars, non_read);
        Option::None
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
    non_read: &mut DoubleIndexedMap,
){
    for var in read_vars.iter() {
        if let Option::Some(id) = found_vars.get_variable(var){
            remove_var(non_read, *id);
        }
        else{
            unreachable!("Found variable not recognized in environment")
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
// |    DoubleIndexedMap manipulation functions   |
// ------------------------------------------------

/// Inserts the pair in both maps. The function assumes that there is
/// no entry for var->subs, so if a useless substitution has been detected
/// it should have been previously detected and removed
fn insert_pair(
    map: &mut DoubleIndexedMap,
    var: IdVar,
    subs: IdSubs,
    depth: u32,
) {
    map.subs_to_var.insert(subs, (var, depth));
    if !map.var_to_subs.contains_key(&var) {
        map.var_to_subs.insert(var, HashSet::new());
    }
    if let Option::Some(set) = map.var_to_subs.get_mut(&var){
        set.insert((subs, depth));
    }
    else{
        unreachable!("key has been checked to be present in map")
    }
}

fn contains_var(
    map: &DoubleIndexedMap,
    var: &IdVar,
) -> bool {
    map.var_to_subs.contains_key(var)
}

fn contains_subs(
    map: &DoubleIndexedMap,
    subs: &IdSubs,
) -> bool {
    map.subs_to_var.contains_key(subs)
}

fn get_var_content(
    map: &DoubleIndexedMap,
    var: IdVar,
) -> Option<&HashSet<(IdSubs, u32)>> {
    map.var_to_subs.get(&var)
}

fn get_subs_content(
    map: &DoubleIndexedMap,
    subs: IdVar,
) -> Option<&(IdVar, u32)> {
    map.subs_to_var.get(&subs)
}

/// Removes all the information related to the variable
/// If the variable was contained in the maps the set of
/// substitutions that had to do with the variable is returned
fn remove_var(
    map: &mut DoubleIndexedMap,
    var: IdVar,
) -> Option<HashSet<(IdSubs, u32)>> {
    if let Option::Some(subs_set) = map.var_to_subs.remove(&var) {
        for (subs, depth) in subs_set.iter() {
            map.subs_to_var.remove(&subs);
        }
        Option::Some(subs_set)
    }
    else{
        Option::None
    }
}

/// Removes all the information related to the substitution
/// If the substitution was contained in the maps the variable
/// of the substitutions returned. If the set of substitutions 
/// for that variable ends up empty, the entry is removed
fn remove_subs(
    map: &mut DoubleIndexedMap,
    subs: IdSubs,
) -> Option<(IdVar,u32)> {
    if let Option::Some((id_var, depth)) = map.subs_to_var.remove(&subs) {
        if let Option::Some(subs_set) = map.var_to_subs.get_mut(&id_var){
            let res = subs_set.remove(&(subs, depth));
            // debug check if the substitution id was related to the variable
            debug_assert!(res);
            if subs_set.is_empty() {
                map.var_to_subs.remove(&id_var);
            }
        }
        else{
            unreachable!("Maps in DoubleIndexedMap are inconsistent")
        }
        Option::Some((id_var, depth))
    }
    else{
        Option::None
    }
}

/// Gets the resulting DoubleIndexedMap of non read variables 
/// to the right non read variables after the execution of both branches.
/// It takes ownership of the second map and returns the result in the first 
/// one. The criteria is the following:
///     - If a substitution of a variable has been done in this current 
///     block or an outer one, to be still non_read it should be non read in
///     both branches.
///     - If a substitution of a variable has been done in an inner block,
///     it will still be non read.
/// 
/// This function also calculates the useless substitutions as the intersection
/// of both sets of useless substitutions. The result is returned in the same
/// way as previously mentioned. 
fn merge_branches(
    map: &mut DoubleIndexedMap,
    useless_set: &mut Option<&mut HashSet<(IdSubs, u32)>>,
    map2: DoubleIndexedMap,
    useless_set2: Option<HashSet<(IdSubs, u32)>>,
    curr_depth: u32,
) {
    if let Option::Some(set1) = useless_set{
        if let Option::Some(set2) = useless_set2{
            set1.retain(|x| set2.contains(x));
        }
        else{
            *useless_set = Option::None;
        }
    }
    // Find substitutions in this block or outer ones that should be 
    // removed because it is not in both maps
    let mut to_remove: Vec<IdSubs> = Vec::new();
    for (id_subs, (_, depth)) in &map.subs_to_var{
        if *depth <= curr_depth && !map2.subs_to_var.contains_key(&id_subs){
            to_remove.push(*id_subs);
        }
    }
    // Remove all that is to be removed
    for subs in to_remove{
        remove_subs(map, subs);
    }

    for (id_subs, (id_var, depth)) in map2.subs_to_var{
        // If this substitution is from an inner block
        // it is non read no matter if it is not in the other map
        // so the result must be the union
        if depth > curr_depth{
            insert_pair(map, id_var, id_subs, depth);
        }
    }
}