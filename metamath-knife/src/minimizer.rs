use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
    time::Instant,
};

use itertools::Itertools;
use metamath_rs::{
    as_str, formula::Substitutions, proof::ProofTreeArray, Database, Formula, Label, StatementRef,
};
use rayon::iter::{ParallelBridge, ParallelIterator};

/// One step of a minimized proof
struct MinimizedStep {
    apply: Label,
    hyps: Box<[usize]>,
    result: Formula,
    substitutions: Box<Substitutions>,
}

impl MinimizedStep {
    fn add_to_proof_tree_array(
        &self,
        stack_buffer: &mut Vec<u8>,
        arr: &mut ProofTreeArray,
        logical_steps_idx: &[Option<usize>],
        db: &Database,
    ) -> Option<usize> {
        let mand_hyps: Vec<_> = self
            .hyps
            .iter()
            .map(|step_idx| logical_steps_idx[*step_idx].unwrap())
            .collect();
        db.build_proof_step(
            self.apply,
            &self.result,
            &mand_hyps.into_boxed_slice(),
            &self.substitutions,
            stack_buffer,
            arr,
        )
    }

    /// Attempt to identify best candidate for minimization among two minimized steps.
    /// Currently returns the step with
    #[inline]
    fn _heuristic(&self, _step_usage: &[usize]) -> usize {
        let mut l = 0;
        for h in self.hyps.iter() {
            l += if *h < 20 {
                1
            } else if *h < 120 {
                2
            } else if *h < 620 {
                3
            } else {
                4
            };
        }
        l
    }

    fn compare_with(&self, other: &MinimizedStep) -> Ordering {
        //        match self.heuristic(step_usage).cmp(&other.heuristic(step_usage)) {
        match self.hyps.cmp(&other.hyps) {
            Ordering::Equal => {}
            ord => return ord,
        }
        self.apply.cmp(&other.apply)
    }
}

/// Attempt to minimize a given statement.
/// Requires: [`Database::stmt_parse_pass`]
pub fn minimize(db: &Database, label_str: &str) {
    let now = Instant::now();
    let mut out = std::io::stdout();
    let sref: metamath_rs::StatementRef<'_> =
        db.statement(label_str.as_bytes()).unwrap_or_else(|| {
            panic!("Label {label_str} does not correspond to an existing statement");
        });
    let label = db.name_result().get_atom(sref.label());
    let original_proof_tree = db.get_proof_tree(sref).unwrap_or_else(|| {
        panic!("Could not get original proof tree for label {label_str}");
    });

    // We build a hashtable with all theorems of the database, indexed by their top node
    // Some theorems, like `mp4an`, have a variable as their top node.
    // Those are stored in `theorem_rest` and will be checked every time.
    let mut theorem_hash = HashMap::new();
    let mut theorem_rest = vec![];
    let provable_typecode = db.grammar_result().provable_typecode();
    for theorem in db
        .statements_range(..label)
        .filter(|s| s.is_assertion() && !sref.discouragements().usage_discouraged)
    {
        let formula = db.stmt_parse_result().get_formula(&theorem).unwrap();
        if formula.get_typecode() == provable_typecode {
            if formula.is_variable_by_path(&[]).unwrap() {
                theorem_rest.push(theorem);
            } else {
                theorem_hash
                    .entry(formula.get_by_path(&[]).unwrap())
                    .or_insert(vec![])
                    .push(theorem);
            }
        }
    }

    // Prepare the list of formulas for each logical step.
    let formulas = original_proof_tree.with_logical_steps(db, |cur, _ix, _stmt, _hyps| {
        proof_step_formula(db, &original_proof_tree, cur, true)
    });

    // Prepare the proof array with the essential hypotheses
    let mut proof_tree = ProofTreeArray::default();
    let mut stack_buffer = vec![];
    let mut logical_steps_idx = vec![]; // For each logical step, stores the corresponding index in the full proof tree array
    for (label, formula) in db.get_frame(label).unwrap().essentials() {
        logical_steps_idx.push(db.build_proof_hyp(
            label,
            formula,
            &mut stack_buffer,
            &mut proof_tree,
        ));
    }
    let essentials_count = logical_steps_idx.len();

    // Iterate through each logical step, and attempt to minimize.
    let mut minimized_steps = vec![];
    for step_formulas in prefixes_asc(formulas.as_slice()).skip(essentials_count + 1) {
        let (target_formula, previous_formulas) = step_formulas.split_last().unwrap();
        println!(
            "Working on step {}: {}...",
            step_formulas.len(),
            target_formula.as_ref(db)
        );
        let step = theorem_hash
            .get(&target_formula.get_by_path(&[]).unwrap())
            .unwrap()
            .iter()
            .chain(theorem_rest.iter())
            .par_bridge()
            .filter_map(|theorem| match_theorem(db, theorem, target_formula, previous_formulas))
            .min_by(|a, b| a.compare_with(b))
            .unwrap_or_else(|| {
                panic!(
                    "No minimization found for formula {}",
                    target_formula.as_ref(db)
                )
            });
        minimized_steps.push(step);
    }

    // Identify which steps have actually been used: start with the qed step and accumulate all dependents
    let mut used_steps = vec![formulas.len() - 1];
    let mut i = 0;
    while i < used_steps.len() {
        if used_steps[i] > essentials_count {
            used_steps.extend_from_slice(&minimized_steps[used_steps[i] - essentials_count].hyps);
        }
        i += 1;
    }
    let used_steps: HashSet<usize> = HashSet::from_iter(used_steps);

    // Finally build the rest of the proof with the minimized steps
    for (idx, step) in minimized_steps.iter().enumerate() {
        if idx < essentials_count || used_steps.contains(&(essentials_count + idx)) {
            logical_steps_idx.push(step.add_to_proof_tree_array(
                &mut stack_buffer,
                &mut proof_tree,
                &logical_steps_idx,
                db,
            ));
        } else {
            logical_steps_idx.push(None);
        }
    }
    proof_tree.qed = minimized_steps
        .last()
        .unwrap()
        .add_to_proof_tree_array(&mut stack_buffer, &mut proof_tree, &logical_steps_idx, db)
        .unwrap();

    // Display the generated proof tree
    proof_tree.calc_indent();
    let _ = db.export_mmp_proof_tree(sref.label(), &proof_tree, &mut out);
    println!(
        "minimize {} {}ms",
        label_str,
        (now.elapsed() * 1000).as_secs()
    );
}

/// Attempt to match the candidate theorem, provided the known step formulas.
fn match_theorem(
    db: &Database,
    candidate_theorem: &StatementRef<'_>,
    target_formula: &Formula,
    step_formulas: &[Formula],
) -> Option<MinimizedStep> {
    let mut substitutions = Substitutions::default();
    let theorem_formula = db.stmt_parse_result().get_formula(candidate_theorem)?;
    target_formula
        .unify(theorem_formula, &mut substitutions)
        .ok()?;

    // Found a theorem which *might* be applied, now we check the hypotheses
    let theorem_label = db
        .name_result()
        .lookup_label(candidate_theorem.label())?
        .atom;
    let frame = db.get_frame(theorem_label)?;
    let essentials: Vec<_> = frame.essentials().collect();
    if essentials.is_empty() {
        // No hypoteses, we're done!
        Some(MinimizedStep {
            apply: theorem_label,
            hyps: Box::new([]),
            result: target_formula.clone(),
            substitutions: Box::new(substitutions),
        })
    } else {
        // Iterate over all possible combination of steps, for each formula.
        essentials
            .iter()
            .map(|(_, hyp_fmla)| {
                step_formulas
                    .iter()
                    .enumerate()
                    .filter_map(|(step_idx, step_fmla)| {
                        let mut subst = substitutions.clone();
                        step_fmla
                            .unify(hyp_fmla, &mut subst)
                            .map(|()| (step_idx, subst))
                            .ok()
                    })
            })
            .multi_cartesian_product()
            .find_map(|hyp_match| {
                let mut hyps = vec![];
                let mut subst = substitutions.clone();
                for (step_idx, step_subst) in hyp_match {
                    subst.extend(&step_subst).ok()?;
                    hyps.push(step_idx);
                }
                Some(MinimizedStep {
                    apply: theorem_label,
                    hyps: hyps.into_boxed_slice(),
                    result: target_formula.clone(),
                    substitutions: Box::new(subst),
                })
            })
    }
}

/// Convert a proof step in a [ProofTreeArray] to the corresponding [Formula].
pub fn proof_step_formula(
    database: &Database,
    proof_tree: &ProofTreeArray,
    tree_index: usize,
    use_provables: bool,
) -> Formula {
    let formula_string = String::from_utf8_lossy(&proof_tree.exprs().unwrap()[tree_index]);
    let nset = database.name_result();
    let grammar = database.grammar_result();
    let typecodes = if use_provables {
        Box::new([grammar.provable_typecode()])
    } else {
        grammar.typecodes()
    };
    typecodes
        .iter()
        .find_map(|tc| {
            grammar
                .parse_string(
                    format!("{} {}", as_str(nset.atom_name(*tc)), formula_string.trim()).as_str(),
                    nset,
                )
                .ok()
        })
        .unwrap_or_else(|| panic!("Could not parse formula: {}", formula_string))
}

/// Utility function to iterate prefixes of slices
/// See [https://stackoverflow.com/questions/68837763/how-to-iterate-prefixes-or-suffixes-of-vec-or-slice-in-rust]
pub fn prefixes_asc<T>(slice: &[T]) -> impl Iterator<Item = &[T]> + DoubleEndedIterator {
    (0..=slice.len()).map(move |len| &slice[..len])
}
