//! Binary that takes as standart in a graph in .gr format, computes an optimal vertex cover and
//! writes the solution to standart out.

use std::error;
use std::io;

use duck_and_cover::{graph::DyUGraph, vc_instance::VCInstance, kernelization::Rule, cust_error::ProcessingError};

pub fn main() -> Result<(), Box<dyn error::Error>> {
    let stdin = io::stdin();
    let stdin = stdin.lock();
    let stdout = io::stdout();
    let mut stdout = stdout.lock();
    let graph = DyUGraph::read_gr(stdin)?;
    let n = graph.num_nodes();
    let mut vci = VCInstance::new(graph);
    let org = vci.clone();
    let priority = &[Rule::SimpleRules, Rule::LinkNode, Rule::Clique];
    let resu = vci.branch_and_reduce(priority)?;

    // Validate
    if !org.validate_solution(&resu) {
        return Err(Box::new(ProcessingError::InvalidSolution));
    }

    VCInstance::write_solution(n, &resu, &mut stdout)?;
    Ok(())
}
