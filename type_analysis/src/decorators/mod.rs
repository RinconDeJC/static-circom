pub mod component_type_inference;
pub mod constants_handler;
pub mod type_reduction;
pub mod substitution_analysis;

pub use substitution_analysis::function_substitution_analysis;
pub use substitution_analysis::template_substitution_analysis;