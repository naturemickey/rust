// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc_data_structures::indexed_set::IdxSet;
use rustc_data_structures::bitslice::BitwiseOperator;
use rustc::mir::*;
use rustc::mir::visit::Visitor;
use analysis::dataflow::{BitDenotation, BlockSets, InitialFlow};
use analysis::local_paths::{LocalPaths, PathId};

#[derive(Copy, Clone)]
pub struct MaybeBorrowed<'a, 'tcx: 'a> {
    mir: &'a Mir<'tcx>,
    local_paths: &'a LocalPaths<'tcx>
}

impl<'a, 'tcx: 'a> MaybeBorrowed<'a, 'tcx> {
    pub fn new(mir: &'a Mir<'tcx>, local_paths: &'a LocalPaths<'tcx>) -> Self {
        MaybeBorrowed { mir, local_paths }
    }
}

impl<'a, 'tcx> BitDenotation for MaybeBorrowed<'a, 'tcx> {
    type Idx = PathId;
    fn name() -> &'static str { "maybe_borrowed" }
    fn bits_per_block(&self) -> usize {
        self.local_paths.total_count()
    }

    fn start_block_effect(&self, _sets: &mut IdxSet<PathId>) {
        // Nothing is borrowed on function entry
    }

    fn statement_effect(&self,
                        sets: &mut BlockSets<PathId>,
                        location: Location) {
        match self.mir[location.block].statements[location.statement_index].kind {
            StatementKind::Assign(_, Rvalue::Ref(.., ref place)) => {
                if let Ok(path) = self.local_paths.place_path(place) {
                    sets.gen(&path);
                }
            }
            StatementKind::StorageDead(local) => {
                sets.kill(&self.local_paths.locals[local]);
            }
            _ => {}
        }

        let mut moves = MoveCollector {
            local_paths: self.local_paths,
            sets
        };
        moves.visit_location(self.mir, location);
    }

    fn terminator_effect(&self,
                         sets: &mut BlockSets<PathId>,
                         location: Location) {
        let mut moves = MoveCollector {
            local_paths: self.local_paths,
            sets
        };
        moves.visit_location(self.mir, location);
    }

    fn propagate_call_return(&self,
                             _in_out: &mut IdxSet<PathId>,
                             _call_bb: BasicBlock,
                             _dest_bb: BasicBlock,
                             _dest_place: &Place) {
        // Nothing to do when a call returns successfully
    }
}

impl<'a, 'tcx> BitwiseOperator for MaybeBorrowed<'a, 'tcx> {
    #[inline]
    fn join(&self, pred1: usize, pred2: usize) -> usize {
        pred1 | pred2 // "maybe" means we union effects of both preds
    }
}

impl<'a, 'tcx> InitialFlow for MaybeBorrowed<'a, 'tcx> {
    #[inline]
    fn bottom_value() -> bool {
        false // bottom = unborrowed
    }
}

struct MoveCollector<'a, 'b: 'a, 'tcx: 'a> {
    local_paths: &'a LocalPaths<'tcx>,
    sets: &'a mut BlockSets<'b, PathId>
}

impl<'a, 'b, 'tcx> Visitor<'tcx> for MoveCollector<'a, 'b, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand, _: Location) {
        if let Operand::Move(ref place) = *operand {
            if let Ok(path) = self.local_paths.place_path(place) {
                 self.sets.kill(&path);
            }
        }
    }
}
