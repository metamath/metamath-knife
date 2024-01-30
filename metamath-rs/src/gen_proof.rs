//! A set of utilities to computionally generate proofs.
//!

use crate::{
    as_str, formula::Substitutions, proof::ProofTreeArray, verify::ProofBuilder, Database, Formula,
    Label,
};

impl Database {
    /// Add a hypothesis step to a proof array
    pub fn build_proof_hyp(
        &self,
        label: Label,
        formula: &Formula,
        stack_buffer: &mut Vec<u8>,
        arr: &mut ProofTreeArray,
    ) -> Option<usize> {
        let nset = self.name_result().clone();
        let token = nset.atom_name(label);
        let address = nset.lookup_label(token)?.address;
        let range = formula.as_ref(self).append_to_stack_buffer(stack_buffer);
        Some(arr.build(address, Vec::default(), stack_buffer, range))
    }

    /// Add a normal step to a proof array
    pub fn build_proof_step(
        &self,
        label: Label,
        formula: &Formula,
        mand_hyps: &[usize],
        substitutions: &Substitutions,
        stack_buffer: &mut Vec<u8>,
        arr: &mut ProofTreeArray,
    ) -> Option<usize> {
        let token = self.name_result().atom_name(label);
        let address = self.name_result().lookup_label(token)?.address;
        let range = formula.as_ref(self).append_to_stack_buffer(stack_buffer);
        let frame = self.get_frame(label)?;
        let mut hyps = vec![];
        for label in frame.floating() {
            let formula = &substitutions.get(label).unwrap_or_else(|| {
                panic!(
                    "While building proof using {}: No substitution for {}",
                    as_str(token),
                    as_str(self.name_result().atom_name(label))
                );
            });
            let proof_tree_index = formula
                .as_ref(self)
                .build_syntax_proof::<usize, Vec<usize>>(stack_buffer, arr);
            hyps.push(proof_tree_index);
        }
        hyps.extend(mand_hyps.iter());
        Some(arr.build(address, hyps, stack_buffer, range))
    }
}
