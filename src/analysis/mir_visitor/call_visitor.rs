// This file is adapted from MIRAI (https://github.com/facebookexperimental/MIRAI)
// Original author: Herman Venter <hermanv@fb.com>
// Original copyright header:

// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::analysis::abstract_domain::AbstractDomain;
use crate::analysis::memory::constant_value::{ConstantValue, FunctionReference};
use crate::analysis::memory::expression::{Expression, ExpressionType};
use crate::analysis::memory::known_names::KnownNames;
use crate::analysis::memory::path::{Path, PathRefinement};
use crate::analysis::memory::symbolic_value::{self, SymbolicValue, SymbolicValueTrait};
use crate::analysis::mir_visitor::block_visitor::BlockVisitor;
use crate::analysis::mir_visitor::body_visitor::BodyVisitor;
use crate::analysis::mir_visitor::type_visitor::get_element_type;
use crate::analysis::numerical::apron_domain::{
    ApronAbstractDomain, ApronDomainType, GetManagerTrait,
};
use crate::analysis::numerical::linear_constraint::LinearConstraintSystem;
use crate::analysis::ownership::ownership_state::OwnershipState;
use crate::checker::assertion_checker::{AssertionChecker, CheckerResult};
use crate::checker::checker_trait::CheckerTrait;
use rug::Integer;
use rustc_hir::def_id::DefId;
// use rustc_middle::mir;
// use rustc_middle::ty::subst::GenericArgsRef;
// use rustc_middle::ty::{Ty, TyKind};
use rustc_middle::mir;
use rustc_middle::ty::{GenericArgsRef, Ty, TyKind, TypingEnv};
use rustc_span::source_map::Spanned;
use rustc_type_ir::TypeVisitableExt;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;

pub struct CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx, DomainType>
where
    DomainType: ApronDomainType,
    ApronAbstractDomain<DomainType>: GetManagerTrait,
{
    /// The upper layer block visitor
    pub block_visitor: &'call mut BlockVisitor<'tcx, 'analysis, 'block, 'compilation, DomainType>,

    /// The callee's DefId
    pub callee_def_id: DefId,

    /// The callee's FunctionReference
    pub callee_func_ref: Option<Rc<FunctionReference>>,

    /// The callee's SymbolicValue
    pub callee_fun_val: Rc<SymbolicValue>,

    /// The callee's generic argument list
    pub callee_generic_arguments: Option<GenericArgsRef<'tcx>>,

    /// The callee's KnownNames
    pub callee_known_name: KnownNames,

    /// The callee's generic arguments' types
    pub callee_generic_argument_map: Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,

    pub args: &'call [Spanned<mir::Operand<'tcx>>],

    /// The actual arguments of the callee, the paths and symbolic values are from the caller
    pub actual_args: &'call [(Rc<Path>, Rc<SymbolicValue>)],

    /// The list of types of the actual arguments
    pub actual_argument_types: &'call [Ty<'tcx>],

    /// The destination where the return value is assigned
    pub destination: mir::Place<'tcx>,

    /// If the arguments are functions, store them
    pub function_constant_args: &'call [(Rc<Path>, Rc<SymbolicValue>)],

    /// The call stack, used to detect recursive calls
    pub call_stack: Vec<DefId>,
}

impl<'call, 'block, 'analysis, 'compilation, 'tcx, DomainType> Debug
    for CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx, DomainType>
where
    DomainType: ApronDomainType,
    ApronAbstractDomain<DomainType>: GetManagerTrait,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "CallVisitor".fmt(f)
    }
}

impl<'call, 'block, 'analysis, 'compilation, 'tcx, DomainType>
    CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx, DomainType>
where
    DomainType: ApronDomainType,
    ApronAbstractDomain<DomainType>: GetManagerTrait,
{
    pub(crate) fn new(
        block_visitor: &'call mut BlockVisitor<'tcx, 'analysis, 'block, 'compilation, DomainType>,
        callee_def_id: DefId,
        callee_generic_arguments: Option<GenericArgsRef<'tcx>>,
        callee_generic_argument_map: Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
        func_const: ConstantValue,
    ) -> CallVisitor<'call, 'block, 'analysis, 'compilation, 'tcx, DomainType> {
        if let ConstantValue::Function(func_ref) = &func_const {
            let callee_known_name = func_ref.known_name;
            let active_calls = block_visitor.body_visitor.call_stack.clone();
            CallVisitor {
                block_visitor, // This is a reference to the caller's block visitor
                callee_def_id,
                callee_func_ref: Some(func_ref.clone()),
                callee_fun_val: Rc::new(func_const.into()),
                callee_generic_arguments,
                callee_known_name,
                callee_generic_argument_map,
                args: &[],
                actual_args: &[],
                actual_argument_types: &[],
                destination: mir::Place::return_place(),
                function_constant_args: &[],
                call_stack: active_calls,
            }
        } else {
            unreachable!("caller should supply a constant function")
        }
    }

    /// Analyze the function based on the current environment (caller's state) and return the post state
    pub fn create_function_post_state(&mut self) -> AbstractDomain<DomainType> {
        debug!(
            "Creating callee's post state, def_id={:?}, type of def_id={:?}",
            self.callee_def_id,
            self.block_visitor
                .body_visitor
                .context
                .tcx
                .type_of(self.callee_def_id)
        );
        // If MIR is available, analyze it
        if self
            .block_visitor
            .body_visitor
            .context
            .tcx
            .is_mir_available(self.callee_def_id)
        {
            // Get initial state from caller's state
            // We need to get all the values that may be used in callee's analysis
            // So here we get all the values that represent heap allocations

            // let init_abstract_value = self.extract_heap_value(&self.block_visitor.state);
            // TODO: try to include all states of the caller
            let init_abstract_value = self.block_visitor.state().clone();

            info!("====== Fixed-Point Algorithm Starts ======");
            debug!(
                "Initializing Fixed point iterator with abstract domain: {:?}",
                init_abstract_value
            );
            let mut body_visitor = BodyVisitor::new(
                self.block_visitor.body_visitor.context,
                self.callee_def_id,
                init_abstract_value,
                self.block_visitor.body_visitor.next_fresh_variable_offset,
                self.call_stack.clone(),
            );
            body_visitor.type_visitor.actual_argument_types = self.actual_argument_types.into();
            body_visitor.type_visitor.generic_arguments = self.callee_generic_arguments;
            body_visitor.type_visitor.generic_argument_map =
                self.callee_generic_argument_map.clone();

            // Initialize initial precondition using arguments of the callee
            body_visitor.init_pre_condition(self.actual_args.to_vec());

            debug!("Running fixed point iterator");
            body_visitor.run();

            // Run the bug detector
            body_visitor.run_checker();

            // Update the fresh variable offset for the next call
            self.block_visitor.body_visitor.next_fresh_variable_offset =
                body_visitor.next_fresh_variable_offset;

            let post = body_visitor.post.clone();
            debug!("Fixed point iterator finishes, post: {:?}", post);
            // // Compute the join of all the basic blocks that contain a return terminator
            // let joined_state = post
            //     .into_iter()
            //     .filter(|(bb, _domain)| body_visitor.result_blocks.contains(bb))
            //     .map(|(_bb, domain)| domain)
            //     .reduce(|state1, state2| state1.join(&state2))
            //     .expect("panic in fold1");
            // return joined_state;
            // example3/case2触发无return block
            let joined_state = post
                .into_iter()
                .filter(|(bb, _domain)| body_visitor.result_blocks.contains(bb))
                .map(|(_bb, domain)| domain)
                .reduce(|state1, state2| state1.join(&state2))
                .unwrap_or_else(|| AbstractDomain::<DomainType>::default()); // 提供一个默认值
            return joined_state;
        } else {
            debug!("Not Found MIR for def_id: {:?}", self.callee_def_id);
        }
        // If MIR is NOT available, return default abstract domain
        // AbstractDomain::default()
        self.block_visitor.state().clone()
    }

    /// Returns the function reference part of the value, if there is one.
    fn get_func_ref(&mut self, val: &Rc<SymbolicValue>) -> Option<Rc<FunctionReference>> {
        let extract_func_ref = |c: &ConstantValue| match c {
            ConstantValue::Function(func_ref) => Some(func_ref.clone()),
            _ => None,
        };
        match &val.expression {
            Expression::CompileTimeConstant(c) => {
                // debug!("Expression::CompileTimeConstant");
                return extract_func_ref(c);
            }
            Expression::Reference(path)
            | Expression::Variable {
                path,
                var_type: ExpressionType::NonPrimitive,
            }
            | Expression::Variable {
                path,
                var_type: ExpressionType::Reference,
            } => {
                // debug!("Expression::Reference/Variable");
                let closure_ty = self
                    .block_visitor
                    .body_visitor
                    .type_visitor
                    .get_path_rustc_type(path, self.block_visitor.body_visitor.current_span);

                let _specialized_closure_ty = self
                    .block_visitor
                    .body_visitor
                    .type_visitor
                    .specialize_generic_argument_type(
                        closure_ty,
                        &self
                            .block_visitor
                            .body_visitor
                            .type_visitor
                            .generic_argument_map,
                    );
                match closure_ty.kind() {
                    TyKind::Closure(def_id, args) => {
                        let args = self
                            .block_visitor
                            .body_visitor
                            .type_visitor
                            .specialize_generic_args(
                                args,
                                &self
                                    .block_visitor
                                    .body_visitor
                                    .type_visitor
                                    .generic_argument_map,
                            );
                        return extract_func_ref(self.block_visitor.visit_function_reference(
                            *def_id,
                            closure_ty,
                            Some(args),
                        ));
                    }
                    TyKind::Ref(_, ty, _) => {
                        if let TyKind::Closure(def_id, args) = ty.kind() {
                            let _specialized_substs = self
                                .block_visitor
                                .body_visitor
                                .type_visitor
                                .specialize_generic_args(
                                    args,
                                    &self
                                        .block_visitor
                                        .body_visitor
                                        .type_visitor
                                        .generic_argument_map,
                                );
                            return extract_func_ref(self.block_visitor.visit_function_reference(
                                *def_id,
                                *ty,
                                Some(args),
                            ));
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        None
    }

    pub fn get_function_post_state(&mut self) -> Option<AbstractDomain<DomainType>> {
        // 获得被调用函数的符号值
        let fun_val = self.callee_fun_val.clone();
        // 获得函数引用
        if let Some(func_ref) = self.get_func_ref(&fun_val) {
            // 如果调用栈不存在这个def_id，则推入调用栈，返回这个函数的post_state
            if !self.call_stack.contains(&func_ref.def_id.unwrap()) {
                self.call_stack.push(func_ref.def_id.unwrap());
                debug!("call stack {:?}", self.call_stack);
                let res = Some(self.create_function_post_state());
                return res;
            }
        }
        // 无法获得函数引用，返回None
        warn!("Failed to get_func_ref");
        None
    }

    /// If the current call is to a well known function for which we don't have a cached summary,
    /// this function will update the environment as appropriate and return true. If the return
    /// result is false, just carry on with the normal logic.
    pub fn handled_as_special_function_call(&mut self) -> bool {
        match self.callee_known_name {
            KnownNames::VecFromRawParts => {
                self.handle_from_raw_parts();
                return true;
            }
            KnownNames::VecWithCapacity => {
                self.handle_vec_with_capacity();
                return true;
            }
            KnownNames::VecReserve => {
                self.handle_vec_reserve();
                return true;
            }
            KnownNames::VecSetLen => {
                debug!("CallVisitor: recognized Vec::set_len call");
                self.handle_vec_set_len();
                return true;
            }
            KnownNames::CheckerVerify => {
                assert!(self.actual_args.len() == 1);
                debug!("Handling special function CheckerVerify");
                // if self.block_visitor.body_visitor.check_for_errors {
                self.report_calls_to_special_functions();
                // }
                // self.actual_args = &self.actual_args[0..1];
                // self.handle_assume();
                return true;
            }
            KnownNames::RustDealloc => {
                return true;
            }
            KnownNames::StdPanickingBeginPanic | KnownNames::StdPanickingBeginPanicFmt => {
                // self.handle_panic();
                return true;
            }
            KnownNames::StdIntoVec => {
                self.handle_into_vec();
                return true;
            }
            KnownNames::CoreOpsIndex => {
                self.handle_index();
                return true;
            }
            KnownNames::StdPtrMutPtrOffset
            | KnownNames::StdPtrConstPtrOffset
            | KnownNames::StdPtrMutPtrAdd
            | KnownNames::StdPtrConstPtrAdd
            | KnownNames::StdPtrMutPtrSub
            | KnownNames::StdPtrConstPtrSub
            | KnownNames::StdPtrConstPtrWrappingOffset
            | KnownNames::StdPtrMutPtrWrappingOffset
            | KnownNames::StdPtrMutPtrWrappingAdd
            | KnownNames::StdPtrConstPtrWrappingAdd
            | KnownNames::StdPtrMutPtrWrappingSub
            | KnownNames::StdPtrConstPtrWrappingSub => {
                return self.handle_offset();
                // return true;
            }
            KnownNames::StdPtrMutPtrByteOffset
            | KnownNames::StdPtrConstPtrByteOffset
            | KnownNames::StdPtrMutPtrByteAdd
            | KnownNames::StdPtrConstPtrByteAdd
            | KnownNames::StdPtrMutPtrByteSub
            | KnownNames::StdPtrConstPtrByteSub
            | KnownNames::StdPtrConstPtrWrappingByteOffset
            | KnownNames::StdPtrMutPtrWrappingByteOffset
            | KnownNames::StdPtrMutPtrWrappingByteAdd
            | KnownNames::StdPtrConstPtrWrappingByteAdd
            | KnownNames::StdPtrMutPtrWrappingByteSub
            | KnownNames::StdPtrConstPtrWrappingByteSub => {
                return self.handle_byte_offset();
                // return true;
            }
            KnownNames::StdPtrConstPtrOffsetFrom | KnownNames::StdPtrMutPtrOffsetFrom => {
                // panic!("{:?}", self.callee_known_name);
                return self.handle_offset_from();
            }
            KnownNames::StdPtrConstPtrByteOffsetFrom | KnownNames::StdPtrMutPtrByteOffsetFrom => {
                // panic!("{:?}", self.callee_known_name);
                return self.handle_offset_from();
            }
            KnownNames::StdSliceIndexGetUncheckedMut => {
                return self.handle_get_unchecked_mut();
            }
            KnownNames::StdSliceIndexGetUnchecked => {
                return self.handle_get_unchecked();
            }
            KnownNames::StdSliceFromRawParts => {
                self.handle_slice_from_raw_parts();
                return true;
            }
            KnownNames::StdFrom => {
                self.handle_from();
                return true;
            }
            KnownNames::StdAsMutPtr | KnownNames::StdAsPtr => {
                // self.handle_as_ptr();
                return self.normally_handle();
            }
            KnownNames::StdIntrinsicsCopy | KnownNames::StdIntrinsicsCopyNonOverlapping => {
                self.handle_copy();
                return true;
            }
            KnownNames::StdPtrRead
            | KnownNames::StdPtrReadUnAligned
            | KnownNames::StdPtrReadVolatile
            | KnownNames::StdPtrConstPtrRead
            | KnownNames::StdPtrMutPtrRead => {
                self.handle_read();
                return true;
            }
            KnownNames::StdMemForget => {
                self.handle_forget();
                return true;
            }
            KnownNames::StdMemMaybeUninitUninit => {
                self.handle_maybe_uninit_uninit();
                return true;
            }
            KnownNames::StdMemUninitialized => {
                self.handle_mem_uninitialized();
                return true;
            }
            KnownNames::StdPtrReplace => {
                return true;
            }
            KnownNames::StdPtrSwap | KnownNames::StdPtrSwapNonOverlapping => {
                return true;
            }
            KnownNames::StdBoxFromRaw => {
                self.handle_box_from_raw();
                return true;
            }
            KnownNames::StdPtrWrite
            | KnownNames::StdPtrWriteBytes
            | KnownNames::StdPtrWriteUnAligned
            | KnownNames::StdPtrWriteVolatile => {
                // return self.handle_write();
                return true;
            }
            KnownNames::StdPtrDropInPlace => {
                return true;
            }
            KnownNames::CoreStrConvertsFromUtf8Unchecked => {
                self.handle_from_utf8_unchecked();
                return self.normally_handle();
            }
            KnownNames::StdMemManuallyDropNew => {
                self.handle_manually_drop_new();
                return true;
            }
            KnownNames::CoreOpsDeref => {
                return self.handle_deref();
            }
            KnownNames::StdBoxIntoRaw => {
                println!("boxintorwa");
                return true;
            }
            KnownNames::StdBoxLeak => {
                self.handle_box_leak();
                return true;
            }
            _ => {
                return self.normally_handle();
            }
        }
    }

    fn normally_handle(&mut self) -> bool {
        let destination_path = Some(self.block_visitor.get_path_for_place(&self.destination));
        let result = self.try_to_inline_special_function();
        if !result.is_bottom() {
            if let Some(target_path) = destination_path {
                // let target_path = self.block_visitor.visit_place(place);
                self.block_visitor
                    .body_visitor
                    .state
                    .update_value_at(target_path.clone(), result);
                // let exit_condition = self.block_visitor.state.entry_condition.clone();
                // self.block_visitor
                //     .state
                //     .exit_conditions
                //     .insert(*target, exit_condition);
                return true;
            }
        }
        false
    }

    /// If the function being called is a special function like mirai_annotations.mirai_verify or
    /// std.panicking.begin_panic then report a diagnostic or create a precondition as appropriate.
    fn report_calls_to_special_functions(&mut self) {
        match self.callee_known_name {
            KnownNames::CheckerVerify => {
                assert!(self.actual_args.len() == 1); // The type checker ensures this.
                let (_, cond) = &self.actual_args[0];
                // let message = self.coerce_to_string(&self.actual_args[1].1);
                let message = Rc::new(String::from("dummy message"));
                self.block_visitor.check_condition(cond, message, false);
            }
            _ => unreachable!(),
        }
    }

    /// Provides special handling of functions that have no MIR bodies or that need to access
    /// internal MIRAI state in ways that cannot be expressed in normal Rust and therefore
    /// cannot be summarized in the standard_contracts crate.
    /// Returns the result of the call, or BOTTOM if the function to call is not a known
    /// special function.
    fn try_to_inline_special_function(&mut self) -> Rc<SymbolicValue> {
        match self.callee_known_name {
            KnownNames::RustAlloc => self.handle_rust_alloc(),
            KnownNames::RustAllocZeroed => self.handle_rust_alloc(),
            KnownNames::StdMemSizeOf => self.handle_size_of(),
            _ => symbolic_value::BOTTOM.into(),
        }
    }

    // /// Removes the heap block and all paths rooted in it from the current environment.
    // fn handle_rust_dealloc(&mut self) -> Rc<SymbolicValue> {
    //     assert!(self.actual_args.len() == 3);

    //     // The current environment is that that of the caller, but the caller is a standard
    //     // library function and has no interesting state to purge.
    //     // The layout path inserted below will become a side effect of the caller and when that
    //     // side effect is refined by the caller's caller, the refinement will do the purge if the
    //     // qualifier of the path is a heap block path.

    //     // Get path to the heap block to deallocate
    //     let heap_block_path = self.actual_args[0].0.clone();

    //     // Create a layout
    //     let length = self.actual_args[1].1.clone();
    //     let alignment = self.actual_args[2].1.clone();
    //     let layout = SymbolicValue::make_from(
    //         Expression::HeapBlockLayout {
    //             length,
    //             alignment,
    //             source: LayoutSource::DeAlloc,
    //         },
    //         1,
    //     );

    //     // Get a layout path and update the environment
    //     let layout_path =
    //         Path::new_layout(heap_block_path).refine_paths(&self.block_visitor.state());
    //     self.block_visitor
    //         .body_visitor
    //         .state
    //         .update_value_at(layout_path, layout);

    //     // Signal to the caller that there is no return result
    //     symbolic_value::BOTTOM.into()
    // }

    /// Returns a new heap memory block with the given byte length.
    fn handle_rust_alloc(&mut self) -> Rc<SymbolicValue> {
        assert!(self.actual_args.len() == 2);
        let length = self.actual_args[0].1.clone();
        let alignment = self.actual_args[1].1.clone();
        let tcx = self.block_visitor.body_visitor.context.tcx;
        let byte_slice = Ty::new_slice(tcx, tcx.types.u8);
        let heap_path = Path::get_as_path(
            self.block_visitor
                .body_visitor
                .get_new_heap_block(length, alignment, byte_slice),
        );
        SymbolicValue::make_reference(heap_path)
    }

    // /// Returns a new heap memory block with the given byte length and with the zeroed flag set.
    // fn handle_rust_alloc_zeroed(&mut self) -> Rc<SymbolicValue> {
    //     assert!(self.actual_args.len() == 2);
    //     let length = self.actual_args[0].1.clone();
    //     let alignment = self.actual_args[1].1.clone();
    //     let tcx = self.block_visitor.body_visitor.context.tcx;
    //     let byte_slice = tcx.mk_slice(tcx.types.u8);
    //     let heap_path = Path::get_as_path(
    //         self.block_visitor
    //             .body_visitor
    //             .get_new_heap_block(length, alignment, true, byte_slice),
    //     );
    //     SymbolicValue::make_reference(heap_path)
    // }

    // /// Sets the length of the heap block to a new value and removes index paths as necessary
    // /// if the new length is known and less than the old lengths.
    // fn handle_rust_realloc(&mut self) -> Rc<SymbolicValue> {
    //     assert!(self.actual_args.len() == 4);
    //     // Get path to the heap block to reallocate
    //     let heap_block_path = Path::new_deref(self.actual_args[0].0.clone());

    //     // Create a layout
    //     let length = self.actual_args[1].1.clone();
    //     let alignment = self.actual_args[2].1.clone();
    //     let new_length = self.actual_args[3].1.clone();
    //     // We need to this to check for consistency between the realloc layout arg and the
    //     // initial alloc layout.
    //     let layout_param = SymbolicValue::make_from(
    //         Expression::HeapBlockLayout {
    //             length,
    //             alignment: alignment.clone(),
    //             source: LayoutSource::ReAlloc,
    //         },
    //         1,
    //     );
    //     // We need this to keep track of the new length
    //     let new_length_layout = SymbolicValue::make_from(
    //         Expression::HeapBlockLayout {
    //             length: new_length,
    //             alignment,
    //             source: LayoutSource::ReAlloc,
    //         },
    //         1,
    //     );

    //     // Get a layout path and update the environment
    //     let layout_path =
    //         Path::new_layout(heap_block_path).refine_paths(&self.block_visitor.state());
    //     self.block_visitor
    //         .body_visitor
    //         .state
    //         .update_value_at(layout_path.clone(), new_length_layout);
    //     let layout_path2 = Path::new_layout(layout_path);
    //     self.block_visitor
    //         .body_visitor
    //         .state
    //         .update_value_at(layout_path2, layout_param);

    //     // Return the original heap block reference as the result
    //     self.actual_args[0].1.clone()
    // }

    // /// Set the call result to an offset derived from the arguments. Does no checking.
    // fn handle_arith_offset(&mut self) -> Rc<SymbolicValue> {
    //     assert!(self.actual_args.len() == 2);
    //     let base_val = &self.actual_args[0].1;
    //     let offset_val = &self.actual_args[1].1;
    //     base_val.offset(offset_val.clone())
    // }

    // /// Set the call result to an offset derived from the arguments.
    // /// Checks that the resulting offset is either in bounds or one
    // /// byte past the end of an allocated object.
    // fn handle_offset(&mut self) -> Rc<SymbolicValue> {
    //     assert!(self.actual_args.len() == 2);
    //     let base_val = &self.actual_args[0].1;
    //     let offset_val = &self.actual_args[1].1;
    //     let result = base_val.offset(offset_val.clone());

    //     let solver = &self.block_visitor.body_visitor.z3_solver;

    //     let base = Path::get_as_path(self.actual_args[0].1.clone());
    //     let base_len = Path::new_field(base, 1);
    //     let offset = self.actual_args[1].0.clone();

    //     let constraint_system =
    //         LinearConstraintSystem::from(&self.block_visitor.state().numerical_domain);
    //     for cst in &constraint_system {
    //         solver.assert(&solver.get_as_z3_expression(cst));
    //     }

    //     let mut exp = LinearExpression::default();
    //     exp = exp + base_len - offset;
    //     let cst = LinearConstraint::LessEq(exp);
    //     solver.assert(&solver.get_as_z3_expression(&cst));

    //     let solver_result = solver.solve();
    //     solver.reset();

    //     if solver_result == SmtResult::Sat {
    //         let warning = self
    //             .block_visitor
    //             .body_visitor
    //             .context
    //             .session
    //             .dcx().struct_span_warn(
    //                 self.block_visitor.body_visitor.current_span,
    //                 format!("Possible out-of-bound offset").as_str(),
    //             );
    //         self.block_visitor
    //             .body_visitor
    //             .emit_diagnostic(warning, true);
    //     } else {
    //         debug!("Proved that offset is safe!");
    //     }

    //     // if self.block_visitor.body_visitor.check_for_errors && self.function_being_analyzed_is_root() {
    //     //     self.check_offset(&result)
    //     // }
    //     result
    // }

    /// Handle deref call
    fn handle_deref(&mut self) -> bool {
        assert!(self.actual_args.len() == 1);

        // 获取目标路径 - 仿照 handle_index 的模式
        #[allow(irrefutable_let_patterns)]
        let destination_path = if let dest = self.destination {
            Some(self.block_visitor.get_path_for_place(&dest))
        } else {
            None
        };
        assert!(destination_path.is_some());

        // 获取操作数路径和值
        let operand_path = &self.actual_args[0].0;
        let result = destination_path.as_ref().unwrap();

        // 创建解引用后的值
        let deref_path = Path::new_deref(operand_path.clone());

        let deref_val = SymbolicValue::make_reference(
            deref_path.refine_paths(&self.block_visitor.body_visitor.state),
        );

        // 更新状态 - 将解引用的结果赋值给目标路径
        self.block_visitor
            .body_visitor
            .state
            .update_value_at(result.clone(), deref_val);

        true
    }

    /// Gets the size in bytes of the type parameter T of the std::mem::size_of<T> function.
    /// Returns and unknown value of type u128 if T is not a concrete type.
    fn handle_size_of(&mut self) -> Rc<SymbolicValue> {
        assert!(self.actual_args.is_empty());
        let sym = rustc_span::Symbol::intern("T");
        let t = (self.callee_generic_argument_map.as_ref())
            .expect("std::mem::size_of must be called with generic arguments")
            .get(&sym)
            .expect("std::mem::size must have generic argument T");
        // let param_env = self
        //     .block_visitor
        //     .body_visitor
        //     .context
        //     .tcx
        //     .param_env(self.callee_def_id);
        if let Ok(ty_and_layout) = self.block_visitor.body_visitor.type_visitor.layout_of(*t) {
            Rc::new((ty_and_layout.layout.size.bytes() as u128).into())
        } else {
            // SymbolicValue::make_typed_unknown(ExpressionType::U128)
            Rc::new(symbolic_value::TOP)
        }
    }

    /// std::mem::uninitialized::<T>()
    /// 将目标路径的 ownership_state 初始化为 Uinit
    fn handle_mem_uninitialized(&mut self) {
        assert!(self.actual_args.is_empty());

        let dst_path = self.block_visitor.get_path_for_place(&self.destination);
        info!(
            "mem::uninitialized - mark destination path as Uinit: {:?}",
            dst_path
        );

        self.block_visitor
            .body_visitor
            .state
            .ownership_domain
            .set_state(dst_path.clone(), OwnershipState::Uinit);
    }

    /// mem::MaybeUninit::uninit()
    /// 返回一个未初始化的 MaybeUninit<T>，将其抽象为 Uinit
    fn handle_maybe_uninit_uninit(&mut self) {
        assert!(self.actual_args.is_empty());

        let dst_path = self.block_visitor.get_path_for_place(&self.destination);
        info!(
            "mem::MaybeUninit::uninit - mark destination path as Uinit: {:?}",
            dst_path
        );

        self.block_visitor
            .body_visitor
            .state
            .ownership_domain
            .set_state(dst_path.clone(), OwnershipState::Uinit);
    }

    fn handle_box_from_raw(&mut self) {
        assert!(self.actual_args.len() == 1);
        
        // 第一个参数是指针 (ptr: *mut T)
        let src_ptr_path = self.actual_args[0].0.clone();
        let src_ptr_value = self.actual_args[0].1.clone();
        
        info!("=== Starting Box::from_raw handling ===");
        
        // 从指针符号值中提取实际的源路径（可能有多个，如果是 Join）
        let src_paths = self.extract_path_from_ptr_value(&src_ptr_value, &src_ptr_path);
        
        info!("Box::from_raw - source paths: {:?}", src_paths);
        
        // 获取目标路径（返回值）
        let dst_path = self.block_visitor.get_path_for_place(&self.destination);
        info!("Box::from_raw - destination path: {:?}", dst_path);
        
        // Box 总是需要管理内存，所以直接进行所有权跟踪
        // 不需要检查 needs_drop，因为 Box 本身总是需要 drop 来释放内存
        info!("Box::from_raw - applying ownership tracking (Box always manages memory)");
        
        // 对所有可能的源路径进行处理
        for src_path in &src_paths {
            // 在并查集中标记源和目标共享同一资源
            // 这用于检测 double free：如果源和目标都 drop，会导致 double free
            self.block_visitor
                .body_visitor
                .state
                .ownership_domain
                .shared_resources
                .union(src_path, &dst_path);
            
            info!(
                "Box::from_raw - marked paths as sharing the same resource: {:?} <-> {:?}",
                src_path, dst_path
            );
        }
        
        // 目标获得了所有权，标记为 Owned 状态
        self.block_visitor
            .body_visitor
            .state
            .ownership_domain
            .set_state(dst_path.clone(), OwnershipState::Owned);
        
        info!("Box::from_raw - successfully updated ownership states");
        info!("=== Finished Box::from_raw handling ===");
    }

    fn handle_into_vec(&mut self) {
        assert!(self.actual_args.len() == 1);
        let source = &self.actual_args[0].0;
        #[allow(irrefutable_let_patterns)]
        let destination_path = if let dest = self.destination {
            Some(self.block_visitor.get_path_for_place(&dest))
        } else {
            None
        };
        assert!(destination_path.is_some());

        let result = destination_path.as_ref().unwrap();

        let body_visitor = &mut self.block_visitor.body_visitor;
        let rtype = body_visitor
            .type_visitor
            .get_path_rustc_type(source, body_visitor.current_span);
        self.block_visitor
            .copy_or_move_elements(result.clone(), source.clone(), rtype, true);
    }

    fn handle_from_raw_parts(&mut self) {
        assert!(self.actual_args.len() == 3);
        
        // 第一个参数是指针 (ptr: *mut T)
        let src_ptr_path = self.actual_args[0].0.clone();
        let src_ptr_value = self.actual_args[0].1.clone();
        
        info!("=== Starting Vec::from_raw_parts handling ===");
        
        // 从指针符号值中提取实际的源路径（可能有多个，如果是 Join）
        let src_paths = self.extract_path_from_ptr_value(&src_ptr_value, &src_ptr_path);
        
        info!("Vec::from_raw_parts - source paths: {:?}", src_paths);
        
        // 获取目标路径（返回值）
        let dst_path = self.block_visitor.get_path_for_place(&self.destination);
        info!("Vec::from_raw_parts - destination path: {:?}", dst_path);
        
        // Vec 总是需要管理内存，所以直接进行所有权跟踪
        // 不需要检查 needs_drop，因为 Vec 本身总是需要 drop 来释放内存
        info!("Vec::from_raw_parts - applying ownership tracking (Vec always manages memory)");
        
        // 对所有可能的源路径进行处理
        for src_path in &src_paths {
            // 在并查集中标记源和目标共享同一资源
            // 这用于检测 double free：如果源和目标都 drop，会导致 double free
            self.block_visitor
                .body_visitor
                .state
                .ownership_domain
                .shared_resources
                .union(src_path, &dst_path);
            
            info!(
                "Vec::from_raw_parts - marked paths as sharing the same resource: {:?} <-> {:?}",
                src_path, dst_path
            );
        }
        
        // 目标获得了所有权，标记为 Owned 状态
        self.block_visitor
            .body_visitor
            .state
            .ownership_domain
            .set_state(dst_path.clone(), OwnershipState::Owned);
        
        info!("Vec::from_raw_parts - successfully updated ownership states");
        info!("=== Finished Vec::from_raw_parts handling ===");
    }

    /// Vec::with_capacity
    /// 当前抽象：将返回的 Vec 标记为 Uinit，以便后续对其内容的访问能被检查出来。
    fn handle_vec_with_capacity(&mut self) {
        // Vec::with_capacity(capacity)
        assert!(self.actual_args.len() == 1);

        let dst_path = self.block_visitor.get_path_for_place(&self.destination);
        info!(
            "Vec::with_capacity - mark destination path as Uinit: {:?}",
            dst_path
        );

        self.block_visitor
            .body_visitor
            .state
            .ownership_domain
            .set_state(dst_path.clone(), OwnershipState::Uinit);
    }

    /// Vec::reserve
    /// 当 Vec 调用 reserve 后，如果后续调用 set_len，可能会暴露未初始化内存。
    /// 将 Vec 标记为 Uinit，与 with_capacity 一样处理。
    fn handle_vec_reserve(&mut self) {
        // Vec::reserve(&mut self, additional)
        // 第一个参数是 &mut self，第二个参数是 additional
        assert!(self.actual_args.len() == 2);

        // 从引用符号值中提取实际的 Vec 路径
        let vec_arg_value = self.actual_args[0].1.clone();
        let actual_vec_path = match &vec_arg_value.expression {
            Expression::Reference(path) => {
                info!("Vec::reserve - extracted actual vec path from reference: {:?}", path);
                path.clone()
            }
            _ => {
                warn!("Vec::reserve - vec arg value is not a reference, using arg path: {:?}", self.actual_args[0].0);
                self.actual_args[0].0.clone()
            }
        };

        info!(
            "Vec::reserve - mark vec path as Uinit: {:?}",
            actual_vec_path
        );

        // 将 Vec 标记为 Uinit，这样后续 set_len 会被检测到
        self.block_visitor
            .body_visitor
            .state
            .ownership_domain
            .set_state(actual_vec_path.clone(), OwnershipState::Uinit);
    }

    /// Vec::set_len
    /// 当 Vec 通过 set_len 设置长度时，新增加的元素仍然是未初始化的。
    /// 如果 Vec 之前是 Uinit 状态，set_len 后仍然保持 Uinit 状态。
    /// 
    /// 特别地，如果 Vec 是通过 with_capacity 或 reserve 创建的（已经是 Uinit），
    /// 调用 set_len 会暴露未初始化内存，应该在这里直接发出警告。
    fn handle_vec_set_len(&mut self) {
        // Vec::set_len(self, len)
        // 第一个参数是 &mut self，第二个参数是 len
        assert!(self.actual_args.len() == 2);

        // 第一个参数是 &mut self，即 Vec 本身的引用
        // actual_args[0] 是 (path, value)，其中 value 可能是 Expression::Reference(actual_vec_path)
        let vec_arg_path = self.actual_args[0].0.clone();
        let vec_arg_value = self.actual_args[0].1.clone();
        let len_value = self.actual_args[1].1.clone();
        
        info!("=== Starting Vec::set_len handling ===");
        info!("Vec::set_len - vec arg path: {:?}", vec_arg_path);
        info!("Vec::set_len - vec arg value: {:?}", vec_arg_value);
        info!("Vec::set_len - len value: {:?}", len_value);

        let body_visitor = &mut self.block_visitor.body_visitor;
        let current_span = body_visitor.current_span;

        // 从引用符号值中提取实际的 Vec 路径
        // vec_arg_value 是 &(local_4) 这样的引用，我们需要提取 local_4
        let actual_vec_path = match &vec_arg_value.expression {
            Expression::Reference(path) => {
                // 这是引用，直接使用被引用的路径
                info!("Vec::set_len - extracted actual vec path from reference: {:?}", path);
                path.clone()
            }
            _ => {
                // 如果不是引用，尝试从路径中提取（可能是直接路径）
                // 如果路径本身指向引用，需要解引用
                warn!("Vec::set_len - vec arg value is not a reference, using arg path: {:?}", vec_arg_path);
                vec_arg_path.clone()
            }
        };

        info!("Vec::set_len - actual vec path to check: {:?}", actual_vec_path);

        // 检查 Vec 的当前状态
        let states = body_visitor
            .state
            .ownership_domain
            .get_states(&actual_vec_path);

        info!("Vec::set_len - vec states: {:?}", states);

        // 如果 Vec 是 Uinit 状态（通常是通过 with_capacity 或 reserve 创建的），
        // set_len 会暴露未初始化内存，应该发出警告
        if states.contains(&OwnershipState::Uinit) {
            // Vec 已经是 Uinit 状态，set_len 会暴露未初始化内存
            // 这可能是通过 with_capacity 或 reserve 创建的
            let warning = body_visitor
                .context
                .session
                .dcx()
                .struct_span_warn(
                    current_span,
                    "[Checker] Provably unsafe error: Vec::set_len called on uninitialized Vec (created via with_capacity or reserve), exposing uninitialized memory",
                );
            warning.emit();
            info!("Vec::set_len - detected set_len on uninitialized Vec, warning emitted");
        }

        // 如果 Vec 不是 Uinit 状态，set_len 会将新增加的部分标记为 Uinit
        // 为了保守起见，我们总是将 Vec 标记为 Uinit
        if !states.contains(&OwnershipState::Uinit) {
            // Vec 之前不是 Uinit，但 set_len 后新增加的部分是未初始化的
            // 我们需要将整个 Vec 标记为 Uinit（因为现在包含未初始化的部分）
            body_visitor
                .state
                .ownership_domain
                .set_state(actual_vec_path.clone(), OwnershipState::Uinit);
            
            info!("Vec::set_len - marked vec as Uinit (new elements are uninitialized)");
        } else {
            info!("Vec::set_len - vec already marked as Uinit");
        }

        info!("=== Finished Vec::set_len handling ===");
    }

    /// core::slice::from_raw_parts
    /// 保守建模：将返回的切片视为可能包含未初始化字节，统一标记为 Uinit，
    /// 这样后续对切片的索引访问（bytes[i]）会被 Uinit 检查拦截。
    /// 
    /// 同时检查指针参数的有效性：
    /// 1. 检查指针是否为 null
    /// 2. 检查指针是否无法追溯到有效的内存路径（如从整数转换的指针）
    /// 3. 检查指针是否为编译时常量（可能是无效的）
    fn handle_slice_from_raw_parts(&mut self) {
        // from_raw_parts(ptr, len)
        assert!(self.actual_args.len() == 2);

        let ptr_path = self.actual_args[0].0.clone();
        let ptr_value = self.actual_args[0].1.clone();
        let len_value = self.actual_args[1].1.clone();

        info!("=== Starting slice::from_raw_parts handling ===");
        info!("slice::from_raw_parts - pointer path: {:?}", ptr_path);
        info!("slice::from_raw_parts - pointer value: {:?}", ptr_value);
        info!("slice::from_raw_parts - length value: {:?}", len_value);

        // 检查指针的有效性
        self.check_slice_from_raw_parts_pointer(&ptr_value, &ptr_path, &len_value);

        let dst_path = self.block_visitor.get_path_for_place(&self.destination);
        info!(
            "slice::from_raw_parts - mark destination slice path as Uinit: {:?}",
            dst_path
        );

        self.block_visitor
            .body_visitor
            .state
            .ownership_domain
            .set_state(dst_path.clone(), OwnershipState::Uinit);

        info!("=== Finished slice::from_raw_parts handling ===");
    }

    /// 检查 slice::from_raw_parts 的指针参数是否有效
    fn check_slice_from_raw_parts_pointer(
        &mut self,
        ptr_value: &Rc<SymbolicValue>,
        ptr_path: &Rc<Path>,
        len_value: &Rc<SymbolicValue>,
    ) {
        info!("=== Starting slice::from_raw_parts pointer validation ===");
        info!("check_slice_from_raw_parts_pointer - pointer value: {:?}", ptr_value);
        info!("check_slice_from_raw_parts_pointer - pointer path: {:?}", ptr_path);

        let body_visitor = &mut self.block_visitor.body_visitor;
        let current_span = body_visitor.current_span;

        // 检查1: 指针是否为编译时常量或从编译时常量转换而来（可能是从整数转换的无效指针）
        // 需要检查 Cast 表达式，因为 0x1usize as *const u8 会被表示为 Cast
        let (is_compile_time_constant, constant_value) = match &ptr_value.expression {
            Expression::CompileTimeConstant(ConstantValue::Int(val)) => {
                (true, Some(val.clone()))
            }
            Expression::Cast { operand, .. } => {
                // 检查 Cast 的操作数是否是编译时常量
                if operand.is_compile_time_constant() {
                    if let Some(int_val) = operand.as_int_if_known() {
                        (true, Some(int_val))
                    } else {
                        (false, None)
                    }
                } else {
                    (false, None)
                }
            }
            _ => (false, None),
        };

        if is_compile_time_constant {
            if let Some(int_val) = constant_value {
                if int_val == Integer::from(0) {
                    // Null 指针
                    let warning = body_visitor
                        .context
                        .session
                        .dcx()
                        .struct_span_warn(
                            current_span,
                            "[Checker] Provably unsafe error: slice::from_raw_parts called with null pointer",
                        );
                    warning.emit();
                    info!("check_slice_from_raw_parts_pointer - detected null pointer");
                } else {
                    // 非零的编译时常量指针（可能是从整数转换的无效指针，如 0x1usize as *const u8）
                    let warning = body_visitor
                        .context
                        .session
                        .dcx()
                        .struct_span_warn(
                            current_span,
                            format!(
                                "[Checker] Provably unsafe error: slice::from_raw_parts called with potentially invalid pointer (compile-time constant: {})",
                                int_val
                            ),
                        );
                    warning.emit();
                    info!("check_slice_from_raw_parts_pointer - detected compile-time constant pointer: {}", int_val);
                }
            }
        }

        // 检查2: 指针是否无法追溯到有效的内存路径
        // 先检查指针表达式类型，避免借用冲突
        let can_extract_path = match &ptr_value.expression {
            Expression::Reference(_) | Expression::Variable { .. } | Expression::Offset { .. } => true,
            Expression::CompileTimeConstant(_) => false, // 编译时常量无法提取路径
            Expression::Cast { .. } => {
                // Cast 表达式需要检查操作数
                false // 如果 Cast 的操作数是编译时常量，上面已经检查过了
            }
            _ => false,
        };

        if !can_extract_path && !is_compile_time_constant {
            // 无法提取有效路径，可能是无效指针
            // 但需要排除一些已知的安全情况
            let is_known_safe = match &ptr_value.expression {
                Expression::Top | Expression::Bottom => true,
                _ => false,
            };
            
            if !is_known_safe {
                let warning = body_visitor
                    .context
                    .session
                    .dcx()
                    .struct_span_warn(
                        current_span,
                        "[Checker] Possible unsafe error: slice::from_raw_parts called with pointer that cannot be traced to valid memory",
                    );
                warning.emit();
                info!("check_slice_from_raw_parts_pointer - cannot extract valid path from pointer");
            }
        } else if can_extract_path {
            // 对于可以提取路径的情况，我们暂时跳过详细检查
            // 因为 extract_path_from_ptr_value 需要不可变借用，而我们在可变借用上下文中
            // 这个检查主要是为了捕获编译时常量指针，已经在上面的检查中处理了
            info!("check_slice_from_raw_parts_pointer - pointer expression suggests valid path");
        }

        // 检查3: 如果长度不为0，确保指针非null
        if let Some(len_int) = len_value.as_int_if_known() {
            if len_int > Integer::from(0) {
                // 长度大于0，指针必须非null
                // 如果指针是编译时常量且为0，上面已经检查过了
                // 这里可以添加更复杂的检查，比如使用 AssertionChecker 来验证指针非null
                if is_compile_time_constant {
                    if let Some(ptr_int) = ptr_value.as_int_if_known() {
                        if ptr_int == Integer::from(0) {
                            // 已经在上面检查过了
                        }
                    }
                }
            }
        }

        info!("=== Finished slice::from_raw_parts pointer validation ===");
    }

    fn handle_as_ptr(&mut self) {
        assert!(self.actual_args.len() == 1);
        let src_path = self.actual_args[0].0.clone();

        info!("=== Starting as_ptr/as_mut_ptr handling ===");
        info!("as_ptr - source path: {:?}", src_path);

        // 获取目标路径（返回值）
        let dst_path = self.block_visitor.get_path_for_place(&self.destination);
        info!("as_ptr - destination path: {:?}", dst_path);

        // 创建指向源路径第一个元素的引用
        // 对于数组/切片，.0 表示第一个元素
        
        let ptr_value = SymbolicValue::make_reference(src_path);
        
        self.block_visitor.body_visitor.state.ownership_domain.heap_owner_set.insert(dst_path.clone());

        // 更新目标路径的值
        self.block_visitor
            .body_visitor
            .state
            .update_value_at(dst_path.clone(), ptr_value);

        info!("as_ptr - created pointer reference to first element");
        info!("=== Finished as_ptr/as_mut_ptr handling ===");
    }

    fn handle_from(&mut self) {
        assert!(self.actual_args.len() == 1);
        let source = &self.actual_args[0].0;
        #[allow(irrefutable_let_patterns)]
        let destination_path = if let dest = self.destination {
            Some(self.block_visitor.get_path_for_place(&dest))
        } else {
            None
        };
        // assert!(destination_path.is_some());
        let result = destination_path.as_ref().unwrap();

        let body_visitor = &mut self.block_visitor.body_visitor;
        let rtype = body_visitor
            .type_visitor
            .get_path_rustc_type(source, body_visitor.current_span);
        self.block_visitor
            .copy_or_move_elements(result.clone(), source.clone(), rtype, true);
    }

    fn get_ptr_base(&mut self, ptr: &Rc<SymbolicValue>) -> Option<Rc<Path>> {
        match &ptr.expression {
            Expression::Reference(path) => Some(path.clone()),
            Expression::Variable { path, .. } => Some(path.clone()),
            Expression::Offset { left, right: _ } => {
                return self.get_ptr_base(left);
            }
            _ => None,
        }
    }

    // 假设已知来源于同一个指针
    fn get_ptr_diff(
        &mut self,
        ptr1: &Rc<SymbolicValue>,
        ptr2: &Rc<SymbolicValue>,
    ) -> Rc<SymbolicValue> {
        match (&ptr1.expression, &ptr2.expression) {
            (
                Expression::Offset { left: _, right },
                Expression::Offset {
                    left: _,
                    right: right2,
                },
            ) => {
                return right2.sub(right.clone());
            }
            (_, Expression::Offset { left: _, right }) => {
                return right.clone();
            }
            (Expression::Offset { left: _, right }, _) => {
                let zero_val = SymbolicValue::make_from(
                    Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(0))),
                    1,
                );
                return zero_val.sub(right.clone());
            }
            (_, _) => {
                let zero_val = SymbolicValue::make_from(
                    Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(0))),
                    1,
                );
                return zero_val;
            }
        }
    }

    fn get_type_size(&mut self, base: &Rc<Path>) -> Expression {
        let target_type = get_element_type(
            self.block_visitor
                .body_visitor
                .type_visitor
                .get_path_rustc_type(base, self.block_visitor.body_visitor.current_span),
        );
        let byte_size = self
            .block_visitor
            .body_visitor
            .type_visitor
            .get_type_size(target_type);
        Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(byte_size))).into()
    }

    fn handle_offset_from(&mut self) -> bool {
        assert!(self.actual_args.len() == 2);
        // println!("je");
        let is_byte = match self.callee_known_name {
            KnownNames::StdPtrMutPtrOffsetFrom | KnownNames::StdPtrConstPtrOffsetFrom => false,
            KnownNames::StdPtrMutPtrByteOffsetFrom | KnownNames::StdPtrConstPtrByteOffsetFrom => {
                true
            }
            _ => {
                return false;
            }
        };

        let offset1 = self.actual_args[0].1.clone();
        let offset2 = self.actual_args[1].1.clone();
        // println!("offset1: {:?}", offset1);
        // println!("offset2: {:?}", offset2);
        // println!("ptr base of offset1: {:?}", self.get_ptr_base(&offset1));
        // println!("ptr base of offset2: {:?}", self.get_ptr_base(&offset2));
        // let flag = false;
        match (self.get_ptr_base(&offset1), self.get_ptr_base(&offset2)) {
            (None, None) => {
                return false;
            }
            (None, Some(_)) | (Some(_), None) => {}
            (Some(base1), Some(base2)) => {
                if *base1 == *base2 {
                    // 合法处理
                    let mut result = self.get_ptr_diff(&offset1, &offset2);
                    if is_byte {
                        let base = &self.actual_args[0].0.clone();
                        result = result.mul(SymbolicValue::make_from(self.get_type_size(base), 1));
                    }
                    #[allow(irrefutable_let_patterns)]
                    let destination_path = if let dest = self.destination {
                        Some(self.block_visitor.get_path_for_place(&dest))
                    } else {
                        None
                    };
                    assert!(destination_path.is_some());
                    if let Some(target_path) = destination_path {
                        self.block_visitor
                            .body_visitor
                            .state
                            .update_value_at(target_path.clone(), result);
                        return true;
                    }
                }
            }
        }
        let warning = self
            .block_visitor
            .body_visitor
            .context
            .session
            .dcx()
            .struct_span_warn(
                self.block_visitor.body_visitor.current_span,
                format!("[Checker] Possible unsafe error: the ptr from different object"),
            );
        warning.emit();
        return true;
    }

    fn handle_byte_offset(&mut self) -> bool {
        assert!(self.actual_args.len() == 2);

        let offset_val = match self.callee_known_name {
            KnownNames::StdPtrMutPtrByteOffset
            | KnownNames::StdPtrConstPtrByteOffset
            | KnownNames::StdPtrMutPtrByteAdd
            | KnownNames::StdPtrConstPtrByteAdd
            | KnownNames::StdPtrConstPtrWrappingByteOffset
            | KnownNames::StdPtrMutPtrWrappingByteOffset
            | KnownNames::StdPtrMutPtrWrappingByteAdd
            | KnownNames::StdPtrConstPtrWrappingByteAdd => self.actual_args[1].1.clone(),
            KnownNames::StdPtrMutPtrWrappingByteSub
            | KnownNames::StdPtrConstPtrWrappingByteSub
            | KnownNames::StdPtrMutPtrByteSub
            | KnownNames::StdPtrConstPtrByteSub => {
                let offset_val = self.actual_args[1].1.clone();

                let zero_val = SymbolicValue::make_from(
                    Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(0))),
                    1,
                );
                zero_val.sub(offset_val)
            }
            _ => {
                return false;
            }
        };

        let result = self.check_offset(&offset_val);

        #[allow(irrefutable_let_patterns)]
        let destination_path = if let dest = self.destination {
            Some(self.block_visitor.get_path_for_place(&dest))
        } else {
            None
        };
        assert!(destination_path.is_some());

        if let Some(target_path) = destination_path {
            self.block_visitor
                .body_visitor
                .state
                .update_value_at(target_path.clone(), result);
            return true;
        }
        return false;
    }

    fn handle_get_unchecked(&mut self) -> bool {
        assert!(self.actual_args.len() == 2);
        #[allow(irrefutable_let_patterns)]
        let destination_path = if let dest = self.destination {
            Some(self.block_visitor.get_path_for_place(&dest))
        } else {
            None
        };
        assert!(destination_path.is_some());
        let state = self.block_visitor.state().clone();
        let body_visitor = &mut self.block_visitor.body_visitor;

        let array = &self.actual_args[0].0;
        let array_len = Path::new_length(array.clone()).refine_paths(&body_visitor.state);
        let array_len_val = SymbolicValue::make_from(
            Expression::Variable {
                path: array_len.clone(),
                var_type: ExpressionType::Usize,
            },
            1,
        );
        let index_val = &self.actual_args[1].1;
        let _result = destination_path.as_ref().unwrap();

        let assert_checker = AssertionChecker::new(body_visitor);
        let overflow_safe_cond = SymbolicValue::make_from(
            Expression::LessOrEqual {
                left: index_val.clone(),
                right: array_len_val,
            },
            1,
        );
        let check_result = assert_checker.check_assert_condition(overflow_safe_cond, true, &state);

        // 使用公共方法发出诊断
        Self::emit_unsafe_error(check_result, body_visitor, self.callee_def_id);

        // TODO:这里采用保守方式。
        let result = self.try_to_inline_special_function();
        if !result.is_bottom() {
            if let Some(target_path) = destination_path {
                // let target_path = self.block_visitor.visit_place(place);
                self.block_visitor
                    .body_visitor
                    .state
                    .update_value_at(target_path.clone(), result);
                // let exit_condition = self.block_visitor.state.entry_condition.clone();
                // self.block_visitor
                //     .state
                //     .exit_conditions
                //     .insert(*target, exit_condition);
                return true;
            }
        }
        return false;
    }

    fn handle_get_unchecked_mut(&mut self) -> bool {
        assert!(self.actual_args.len() == 2);
        #[allow(irrefutable_let_patterns)]
        let destination_path = if let dest = self.destination {
            Some(self.block_visitor.get_path_for_place(&dest))
        } else {
            None
        };
        assert!(destination_path.is_some());
        let state = self.block_visitor.state().clone();
        let body_visitor = &mut self.block_visitor.body_visitor;

        let array = &self.actual_args[0].0;
        let array_len = Path::new_length(array.clone()).refine_paths(&body_visitor.state);
        let array_len_val = SymbolicValue::make_from(
            Expression::Variable {
                path: array_len.clone(),
                var_type: ExpressionType::Usize,
            },
            1,
        );
        let index_val = &self.actual_args[1].1;
        let _result = destination_path.as_ref().unwrap();

        let assert_checker = AssertionChecker::new(body_visitor);
        let overflow_safe_cond = SymbolicValue::make_from(
            Expression::LessOrEqual {
                left: index_val.clone(),
                right: array_len_val,
            },
            1,
        );
        let check_result = assert_checker.check_assert_condition(overflow_safe_cond, true, &state);

        // 使用公共方法发出诊断
        Self::emit_unsafe_error(check_result, body_visitor, self.callee_def_id);

        // TODO:这里采用保守方式。
        let result = self.try_to_inline_special_function();
        if !result.is_bottom() {
            if let Some(target_path) = destination_path {
                // let target_path = self.block_visitor.visit_place(place);
                self.block_visitor
                    .body_visitor
                    .state
                    .update_value_at(target_path.clone(), result);
                // let exit_condition = self.block_visitor.state.entry_condition.clone();
                // self.block_visitor
                //     .state
                //     .exit_conditions
                //     .insert(*target, exit_condition);
                return true;
            }
        }
        return false;
    }

    // _3(指针) = offset(_1, _2)
    fn handle_offset(&mut self) -> bool {
        assert!(self.actual_args.len() == 2);
        let base = &self.actual_args[0].0;
        let target_type = get_element_type(
            self.block_visitor
                .body_visitor
                .type_visitor
                .get_path_rustc_type(base, self.block_visitor.body_visitor.current_span),
        );

        let of = &self.actual_args[1].0;
        let of_type = get_element_type(
            self.block_visitor
                .body_visitor
                .type_visitor
                .get_path_rustc_type(of, self.block_visitor.body_visitor.current_span),
        );
        // 判断 of_type 是否为无符号整数类型
        let is_unsigned = match of_type.kind() {
            TyKind::Uint(_) => true, // u8, u16, u32, u64, u128, usize
            _ => false,
        };

        if is_unsigned {
            // 如果是无符号整数，添加 offset >= 0 的约束到数值域中
            // let offset_path = &self.actual_args[1].0;
            let zero_val = SymbolicValue::make_from(
                Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(0))),
                1,
            );

            // 创建 offset >= 0 的表达式
            let offset_ge_zero = SymbolicValue::make_from(
                Expression::GreaterOrEqual {
                    left: self.actual_args[1].1.clone(),
                    right: zero_val,
                },
                1,
            );

            // 将约束添加到数值域中
            match LinearConstraintSystem::try_from(offset_ge_zero.clone()) {
                Ok(constraints) => {
                    self.block_visitor
                        .body_visitor
                        .state
                        .numerical_domain
                        .add_constraints(constraints);

                    debug!("Added constraint: offset >= 0 for unsigned integer type");
                }
                Err(e) => {
                    debug!(
                        "Failed to convert constraint to LinearConstraintSystem: {}",
                        e
                    );
                }
            }
        }

        debug!("of_type is {:?}", of_type);

        let byte_size = self
            .block_visitor
            .body_visitor
            .type_visitor
            .get_type_size(target_type);

        let offset_val = match self.callee_known_name {
            KnownNames::StdPtrMutPtrOffset
            | KnownNames::StdPtrConstPtrOffset
            | KnownNames::StdPtrMutPtrAdd
            | KnownNames::StdPtrConstPtrAdd
            | KnownNames::StdPtrConstPtrWrappingOffset
            | KnownNames::StdPtrMutPtrWrappingOffset
            | KnownNames::StdPtrMutPtrWrappingAdd
            | KnownNames::StdPtrConstPtrWrappingAdd => {
                self.actual_args[1].1.clone().mul(SymbolicValue::make_from(
                    Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(byte_size))),
                    1,
                ))
            }
            KnownNames::StdPtrMutPtrSub
            | KnownNames::StdPtrConstPtrSub
            | KnownNames::StdPtrMutPtrWrappingSub
            | KnownNames::StdPtrConstPtrWrappingSub => {
                let offset_val = self.actual_args[1].1.clone().mul(SymbolicValue::make_from(
                    Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(byte_size))),
                    1,
                ));
                let zero_val = SymbolicValue::make_from(
                    Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(0))),
                    1,
                );
                zero_val.sub(offset_val)
            }
            _ => {
                return false;
            }
        };

        let result = self.check_offset(&offset_val);

        #[allow(irrefutable_let_patterns)]
        let destination_path = if let dest = self.destination {
            Some(self.block_visitor.get_path_for_place(&dest))
        } else {
            None
        };
        assert!(destination_path.is_some());

        if let Some(target_path) = destination_path {
            self.block_visitor
                .body_visitor
                .state
                .update_value_at(target_path.clone(), result);
            return true;
        }
        return false;
    }

    // prepare offset_val for different situation
    fn check_offset(&mut self, old_offset_val: &Rc<SymbolicValue>) -> Rc<SymbolicValue> {
        let base = &self.actual_args[0].0;
        // get the base ptr
        let base_val = &self.actual_args[0].1;
        // calculate the result
        let result = base_val.offset(old_offset_val.clone());
        let mut offset_val = old_offset_val.clone();
        if let Expression::Offset { right, .. } = &result.expression {
            offset_val = right.clone();
        }

        debug!("result: {:?}", result);

        let state = self.block_visitor.state().clone();

        let body_visitor = &mut self.block_visitor.body_visitor;

        // handle array
        let target_type = get_element_type(
            body_visitor
                .type_visitor
                .get_path_rustc_type(base, body_visitor.current_span),
        );
        let byte_size = body_visitor.type_visitor.get_type_size(target_type);
        let base_len = Path::new_length(base.clone()).refine_paths(&body_visitor.state).refine_paths(&body_visitor.state);
        let base_len_val = SymbolicValue::make_from(
            Expression::Variable {
                path: base_len.clone(),
                var_type: ExpressionType::Usize,
            },
            1,
        )
        .mul(SymbolicValue::make_from(
            Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(byte_size))),
            1,
        ));

        // let result = destination_path.as_ref().unwrap();

        // check out of bound access
        let assert_checker = AssertionChecker::new(body_visitor);
        // offset < base.len && offset >= 0
        let overflow_safe_cond = SymbolicValue::make_from(
            Expression::And {
                left: SymbolicValue::make_from(
                    Expression::LessOrEqual {
                        left: offset_val.clone(),
                        right: base_len_val.clone(),
                    },
                    1,
                ),
                right: SymbolicValue::make_from(
                    Expression::GreaterThan {
                        left: offset_val.clone(),
                        right: SymbolicValue::make_from(
                            Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(-1))),
                            1,
                        ),
                    },
                    1,
                ),
            },
            2,
        );

        let check_result = assert_checker.check_assert_condition(overflow_safe_cond, true, &state);
        //  FIXME: 相同Span只能发出一次诊断，未发出的诊断会由编译器进行报错。
        // match check_result {
        //     CheckerResult::Safe => (),
        //     CheckerResult::Unsafe => {
        //         let error = body_visitor.context.session.dcx().struct_span_warn(
        //             body_visitor.current_span,
        //             format!("[Checker] Provably unsafe error: index out of bound",),
        //         );
        //         error.emit();
        //         // body_visitor.emit_diagnostic(error, false, DiagnosticCause::Index);
        //         //return;
        //     }
        //     CheckerResult::Warning => {
        //         let warning = body_visitor.context.session.dcx().struct_span_warn(
        //             body_visitor.current_span,
        //             format!("[Checker] Possible unsafe error: index out of bound"),
        //         );
        //         warning.emit();
        //         // body_visitor.emit_diagnostic(warning, false, DiagnosticCause::Index);
        //     }
        // }
        info!("check_result:{:?}", check_result);
        Self::emit_unsafe_error(check_result, body_visitor, self.callee_def_id);
        result.clone()
    }

    pub fn needs_drop_for_path(&mut self, path: &Rc<Path>, dereference_ptr: bool) -> bool {
        // 获取路径对应的类型
        let mut path_type = self
            .block_visitor
            .body_visitor
            .type_visitor
            .get_path_rustc_type(path, self.block_visitor.body_visitor.current_span);

        info!("needs_drop_for_path - original path_type: {:?}", path_type);

        // 如果需要解引用指针类型，获取指针指向的类型
        if dereference_ptr {
            path_type = match path_type.kind() {
                TyKind::RawPtr(pointee_ty, _) => {
                    info!(
                        "needs_drop_for_path - dereferencing raw pointer to: {:?}",
                        pointee_ty
                    );
                    *pointee_ty
                }
                TyKind::Ref(_, pointee_ty, _) => {
                    info!(
                        "needs_drop_for_path - dereferencing reference to: {:?}",
                        pointee_ty
                    );
                    *pointee_ty
                }
                _ => {
                    info!("needs_drop_for_path - not a pointer type, using original type");
                    path_type
                }
            };
        }

        info!("needs_drop_for_path - checking type: {:?}", path_type);

        // 检查类型是否包含未解析的泛型参数或推断变量，或者是泛型数组
        let is_generic_or_problematic = path_type.has_non_region_param()
            || path_type.has_non_region_infer()
            || matches!(path_type.kind(), TyKind::Array(_, _) | TyKind::Slice(_));

        if is_generic_or_problematic {
            let typing_env = TypingEnv::post_analysis(
                self.block_visitor.body_visitor.context.tcx,
                self.block_visitor.body_visitor.def_id,
            );
            // 对于泛型类型，先检查是否实现了 Copy trait
            let is_copy = self
                .block_visitor
                .body_visitor
                .context
                .tcx
                .type_is_copy_modulo_regions(typing_env, path_type);

            info!("needs_drop_for_path - generic type is_copy: {}", is_copy);

            if is_copy {
                // Copy 类型不需要所有权跟踪
                false
            } else {
                // 对于非 Copy 的泛型类型，保守地假设需要 drop
                true
            }
        } else {
            // 对于具体类型，尝试调用 needs_drop，捕获 panic
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                path_type.needs_drop(
                    self.block_visitor.body_visitor.context.tcx,
                    TypingEnv::fully_monomorphized(),
                )
            })) {
                Ok(result) => {
                    info!("needs_drop_for_path - needs_drop result: {}", result);
                    result
                }
                Err(_) => {
                    warn!("needs_drop_for_path - needs_drop panicked, assuming true");
                    // 保守处理：如果 panic 了就假设需要 drop
                    true
                }
            }
        }
    }

    /// 从符号值表达式中提取路径，支持递归处理 Join 表达式
    /// 返回所有可能的路径集合
    fn extract_paths_from_expression(&self, value: &Rc<SymbolicValue>) -> Vec<Rc<Path>> {
        match &value.expression {
            Expression::Reference(path) => vec![path.clone()],

            Expression::Variable { path, .. } => vec![Path::new_deref(path.clone())],

            Expression::Join { left, right } => {
                let mut paths = Vec::new();
                paths.extend(self.extract_paths_from_expression(left));
                paths.extend(self.extract_paths_from_expression(right));
                paths
            }

            _ => Vec::new(),
        }
    }

    /// 从指针符号值中提取路径，优先使用直接路径，Join 时收集所有路径
    fn extract_path_from_ptr_value(
        &self,
        ptr_value: &Rc<SymbolicValue>,
        fallback_path: &Rc<Path>,
    ) -> Vec<Rc<Path>> {
        let paths = self.extract_paths_from_expression(ptr_value);

        if paths.is_empty() {
            warn!(
                "Unexpected pointer value expression: {:?}, creating deref path from fallback",
                ptr_value.expression
            );
            vec![Path::new_deref(Path::root(fallback_path))]
        } else {
            paths
        }
    }

    fn handle_read(&mut self) {
        assert!(self.actual_args.len() == 1);
        let src_ptr_path = self.actual_args[0].0.clone();
        let src_ptr_value = self.actual_args[0].1.clone();

        info!("=== Starting ptr::read handling ===");

        // 从指针符号值中提取实际的源路径（可能有多个，如果是 Join）
        let src_paths = self.extract_path_from_ptr_value(&src_ptr_value, &src_ptr_path);

        info!("ptr::read - source paths: {:?}", src_paths);
        // 检查源路径是否被 forget
        for src_path in &src_paths {
            let mut is_forgotten = self
                .block_visitor
                .body_visitor
                .state
                .ownership_domain
                .is_forgotten_or_root_forgotten(src_path);

            // 特殊检查：如果有任何路径被forgotten，且当前路径是字段访问，则报错
            if !is_forgotten {
                let all_forgotten_paths: Vec<_> = self
                    .block_visitor
                    .body_visitor
                    .state
                    .ownership_domain
                    .state_map
                    .keys()
                    .filter(|p| {
                        self.block_visitor
                            .body_visitor
                            .state
                            .ownership_domain
                            .is_forgotten_or_root_forgotten(p)
                    })
                    .collect();

                if !all_forgotten_paths.is_empty() {
                    let src_path_str = format!("{:?}", src_path);
                    if src_path_str.contains(".0")
                        || src_path_str.contains(".1")
                        || src_path_str.contains(".2")
                    {
                        is_forgotten = true;
                        info!(
                            "ptr::read - field access {:?} while paths forgotten: {:?}",
                            src_path, all_forgotten_paths
                        );
                    }
                }
            }

            if is_forgotten {
                let warning = self
                    .block_visitor
                    .body_visitor
                    .context
                    .session
                    .dcx()
                    .struct_span_warn(
                        self.block_visitor.body_visitor.current_span,
                        format!(
                            "[Checker] Provably unsafe error: ptr::read from a forgotten path {:?} - accessing memory after mem::forget is undefined behavior",
                            src_path
                        ),
                    );
                warning.emit();
            }
        }


        // 获取目标路径（返回值）
        let dst_path = self.block_visitor.get_path_for_place(&self.destination);
        info!("ptr::read - destination path: {:?}", dst_path);

        // 使用规范化后的目标路径判断是否需要Drop
        let needs_drop = self.needs_drop_for_path(&dst_path, false);
        info!("ptr::read - final needs_drop decision: {}", needs_drop);

        if needs_drop {
            info!("ptr::read - applying ownership tracking for types that need drop");

            // 对所有可能的源路径进行处理
            for src_path in &src_paths {
                // 在并查集中标记源和目标共享同一资源
                self.block_visitor
                    .body_visitor
                    .state
                    .ownership_domain
                    .shared_resources
                    .union(src_path, &dst_path);

                info!(
                    "ptr::read - marked paths as sharing the same resource: {:?} <-> {:?}",
                    src_path, dst_path
                );
            }

            // 目标获得了所有权，标记为 Owned 状态
            self.block_visitor
                .body_visitor
                .state
                .ownership_domain
                .set_state(dst_path.clone(), OwnershipState::Owned);

            info!("ptr::read - successfully updated ownership states");
        }

        info!("=== Finished ptr::read handling ===");
    }

    /// 检查 ptr::copy_nonoverlapping 的目标缓冲区边界
    /// 确保写入操作不会超出目标缓冲区的边界
    fn check_copy_bounds(
        &mut self,
        dst_ptr_value: &Rc<SymbolicValue>,
        dst_ptr_path: &Rc<Path>,
        len_value: &Rc<SymbolicValue>,
    ) {
        info!("=== Starting copy bounds check ===");
        info!("check_copy_bounds - destination pointer value: {:?}", dst_ptr_value);
        info!("check_copy_bounds - destination pointer path: {:?}", dst_ptr_path);
        info!("check_copy_bounds - length value: {:?}", len_value);

        // 从目标指针值中提取基础路径
        let dst_paths = self.extract_path_from_ptr_value(dst_ptr_value, dst_ptr_path);
        
        if dst_paths.is_empty() {
            warn!("check_copy_bounds - cannot extract base path from pointer, skipping bounds check");
            return;
        }

        let state = self.block_visitor.state().clone();
        let current_span = self.block_visitor.body_visitor.current_span;

        // 对每个可能的目标路径进行检查
        for dst_base_path in &dst_paths {
            info!("check_copy_bounds - checking base path: {:?}", dst_base_path);

            // 先获取所有需要的信息，避免多次借用
            let base_len_path = {
                let body_visitor = &self.block_visitor.body_visitor;
                Path::new_length(dst_base_path.clone())
                    .refine_paths(&body_visitor.state)
                    .refine_paths(&body_visitor.state)
            };
            
            let base_len_val = SymbolicValue::make_from(
                Expression::Variable {
                    path: base_len_path.clone(),
                    var_type: ExpressionType::Usize,
                },
                1,
            );

            // 计算指针相对于基础路径的偏移量
            let base_ptr_val = SymbolicValue::make_from(
                Expression::Reference(dst_base_path.clone()),
                1,
            );
            
            let element_offset_val = self.get_ptr_diff(&base_ptr_val, dst_ptr_value);
            info!("check_copy_bounds - calculated element offset: {:?}", element_offset_val);

            // 获取基础路径的元素类型，计算元素大小（字节数）
            let (element_type, byte_size) = {
                let body_visitor = &mut self.block_visitor.body_visitor;
                let base_type = body_visitor
                    .type_visitor
                    .get_path_rustc_type(dst_base_path, current_span);
                let element_type = get_element_type(base_type);
                let byte_size = body_visitor.type_visitor.get_type_size(element_type);
                (element_type, byte_size)
            };
            
            info!("check_copy_bounds - element type: {:?}, byte size: {}", element_type, byte_size);

            // 将元素偏移量转换为字节偏移量
            let byte_offset_val = element_offset_val.mul(SymbolicValue::make_from(
                Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(byte_size))),
                1,
            ));
            
            // 将基础长度从元素数转换为字节数
            let base_len_bytes = base_len_val.mul(SymbolicValue::make_from(
                Expression::CompileTimeConstant(ConstantValue::Int(Integer::from(byte_size))),
                1,
            ));

            info!("check_copy_bounds - byte offset: {:?}, base len bytes: {:?}", byte_offset_val, base_len_bytes);

            // 检查条件：byte_offset + len <= base_len_bytes
            let offset_plus_len = byte_offset_val.add(len_value.clone());
            let safe_cond = SymbolicValue::make_from(
                Expression::LessOrEqual {
                    left: offset_plus_len,
                    right: base_len_bytes,
                },
                1,
            );

            info!("check_copy_bounds - checking condition: offset + len <= base_len");
            
            // 创建 AssertionChecker 并检查
            let check_result = {
                let body_visitor = &mut self.block_visitor.body_visitor;
                let assert_checker = AssertionChecker::new(body_visitor);
                assert_checker.check_assert_condition(safe_cond, true, &state)
            };
            
            info!("check_copy_bounds - check result: {:?}", check_result);
            
            // 发出诊断信息
            match check_result {
                CheckerResult::Unsafe => {
                    let body_visitor = &mut self.block_visitor.body_visitor;
                    let warning = body_visitor
                        .context
                        .session
                        .dcx()
                        .struct_span_warn(
                            body_visitor.current_span,
                            "[Checker] Provably unsafe error: ptr::copy_nonoverlapping writes out of bounds",
                        );
                    warning.emit();
                }
                CheckerResult::Warning => {
                    let body_visitor = &mut self.block_visitor.body_visitor;
                    let warning = body_visitor
                        .context
                        .session
                        .dcx()
                        .struct_span_warn(
                            body_visitor.current_span,
                            "[Checker] Possible unsafe error: ptr::copy_nonoverlapping may write out of bounds",
                        );
                    warning.emit();
                }
                CheckerResult::Safe => {
                    info!("check_copy_bounds - bounds check passed");
                }
            }
        }

        info!("=== Finished copy bounds check ===");
    }

    fn handle_copy(&mut self) {
        assert!(self.actual_args.len() == 3);
        let src_ptr_path = self.actual_args[0].0.clone();
        let src_ptr_value = self.actual_args[0].1.clone();
        let dst_ptr_path = self.actual_args[1].0.clone();
        let dst_ptr_value = self.actual_args[1].1.clone();
        let len_value = self.actual_args[2].1.clone();

        info!("=== Starting ptr::copy handling ===");
        info!("ptr::copy - source pointer path: {:?}", src_ptr_path);
        info!("ptr::copy - destination pointer path: {:?}", dst_ptr_path);
        info!("ptr::copy - length value: {:?}", len_value);

        // 检查目标缓冲区的边界
        self.check_copy_bounds(&dst_ptr_value, &dst_ptr_path, &len_value);

        // 使用辅助方法提取源和目标路径（支持 Join）
        let src_paths = self.extract_path_from_ptr_value(&src_ptr_value, &src_ptr_path);
        let dst_paths = self.extract_path_from_ptr_value(&dst_ptr_value, &dst_ptr_path);

        info!("ptr::copy - extracted source paths: {:?}", src_paths);
        info!("ptr::copy - extracted destination paths: {:?}", dst_paths);

        // 判断目标指针指向的类型是否需要Drop
        // dereference_ptr=true 因为 dst_ptr_path 是指针，需要获取指针指向的类型
        let needs_drop = self.needs_drop_for_path(&dst_ptr_path, true);
        info!("ptr::copy - final needs_drop decision: {}", needs_drop);

        if needs_drop {
            info!("ptr::copy - applying ownership tracking for types that need drop");

            // ptr::copy 会创建一份源数据的副本到目标位置
            // 对所有源路径和目标路径的组合进行处理
            for src_path in &src_paths {
                for dst_path in &dst_paths {
                    // 在并查集中标记源和目标共享同一资源
                    self.block_visitor
                        .body_visitor
                        .state
                        .ownership_domain
                        .shared_resources
                        .union(src_path, dst_path);

                    info!(
                        "ptr::copy - marked paths as sharing the same resource: {:?} <-> {:?}",
                        src_path, dst_path
                    );
                }
            }

            // 设置所有目标路径状态为 Owned（每个目标现在都拥有副本）
            for dst_path in &dst_paths {
                self.block_visitor
                    .body_visitor
                    .state
                    .ownership_domain
                    .set_state(dst_path.clone(), OwnershipState::Owned);

                info!("ptr::copy - set destination path to Owned: {:?}", dst_path);
            }

            info!("ptr::copy - successfully updated ownership states");
        } else {
            info!("ptr::copy - skipping ownership tracking (type doesn't need drop or is Copy)");
        }

        info!("=== Finished ptr::copy handling ===");
    }

    fn handle_box_leak(&mut self) {
        assert!(self.actual_args.len() == 1);
        let arg_path = self.actual_args[0].0.clone();
        let arg_value = self.actual_args[0].1.clone();
    
        info!("=== Starting Box::leak handling ===");
        info!("Box::leak - argument path: {:?}", arg_path);
        info!("Box::leak - argument value: {:?}", arg_value);
    
        // 从参数符号值中提取实际的路径（可能有多个，如果是 Join）
        let actual_arg_paths = self.extract_path_from_ptr_value(&arg_value, &arg_path);
    
        info!(
            "Box::leak - extracted argument paths: {:?}",
            actual_arg_paths
        );
    
        // 第一步：收集所有需要 leak 的路径
        // Box 总是需要管理内存，所以直接收集所有路径
        let mut paths_to_leak = Vec::new();
    
        for actual_arg_path in &actual_arg_paths {
            let needs_drop = self.needs_drop_for_path(actual_arg_path, false);
            info!(
                "Box::leak - path {:?} needs_drop decision: {}",
                actual_arg_path, needs_drop
            );
    
            if needs_drop {
                paths_to_leak.push(actual_arg_path.clone());
            }
        }
    
        // 如果没有需要 leak 的路径，直接返回
        if paths_to_leak.is_empty() {
            info!("Box::leak - no paths need ownership tracking (all are Copy types)");
            info!("=== Finished Box::leak handling ===");
            return;
        }
    
        // 第二步：检查所有需要 leak 的路径是否都可以 forget
        // Box::leak 类似于 forget，会阻止 Box 的 drop
        let mut invalid_paths = Vec::new();
    
        for path in &paths_to_leak {
            if !self
                .block_visitor
                .body_visitor
                .state
                .ownership_domain
                .can_forget(path)
            {
                let states = self
                    .block_visitor
                    .body_visitor
                    .state
                    .ownership_domain
                    .get_states(path);
    
                warn!(
                    "Box::leak - cannot leak path {:?}: invalid ownership state {:?}",
                    path, states
                );
    
                invalid_paths.push((path.clone(), states));
            }
        }
    
        // 如果有任何路径不能 leak，发出警告并跳过所有 leak 操作
        if !invalid_paths.is_empty() {
            let error_details: Vec<String> = invalid_paths
                .iter()
                .map(|(path, states)| format!("{:?} (states: {:?})", path, states))
                .collect();
    
            let warning = self
                .block_visitor
                .body_visitor
                .context
                .session
                .dcx()
                .struct_span_warn(
                    self.block_visitor.body_visitor.current_span,
                    format!(
                        "[Checker] Possible unsafe error: cannot leak Box - invalid ownership states for {} path(s): [{}]",
                        invalid_paths.len(),
                        error_details.join(", ")
                    ),
                );
            warning.emit();
    
            info!("Box::leak - operation aborted due to invalid ownership states");
            info!("=== Finished Box::leak handling ===");
            return;
        }
    
        // 第三步：所有路径都可以 leak，执行 leak 操作
        // Box::leak 会阻止 Box 的 drop，类似于 forget
        info!(
            "Box::leak - all {} paths can be leaked, applying Forgotten state",
            paths_to_leak.len()
        );
    
        for path in &paths_to_leak {
            self.block_visitor
                .body_visitor
                .state
                .ownership_domain
                .add_state(path.clone(), OwnershipState::Forgotten);
    
            info!(
                "Box::leak - successfully added Forgotten state to path: {:?}",
                path
            );
        }
    
        info!(
            "Box::leak - successfully leaked {} path(s)",
            paths_to_leak.len()
        );
        info!("=== Finished Box::leak handling ===");
    }

    fn handle_forget(&mut self) {
        assert!(self.actual_args.len() == 1);
        let arg_path = self.actual_args[0].0.clone();
        let arg_value = self.actual_args[0].1.clone();

        info!("=== Starting mem::forget handling ===");
        info!("mem::forget - argument path: {:?}", arg_path);
        info!("mem::forget - argument value: {:?}", arg_value);

        // 从参数符号值中提取实际的路径（可能有多个，如果是 Join）
        let actual_arg_paths = self.extract_path_from_ptr_value(&arg_value, &arg_path);

        info!(
            "mem::forget - extracted argument paths: {:?}",
            actual_arg_paths
        );

        // 第一步：收集所有需要 forget 的路径
        let mut paths_to_forget = Vec::new();

        for actual_arg_path in &actual_arg_paths {
            let needs_drop = self.needs_drop_for_path(actual_arg_path, false);
            info!(
                "mem::forget - path {:?} needs_drop decision: {}",
                actual_arg_path, needs_drop
            );

            if needs_drop {
                paths_to_forget.push(actual_arg_path.clone());
            }
        }

        // 如果没有需要 forget 的路径，直接返回
        if paths_to_forget.is_empty() {
            info!("mem::forget - no paths need ownership tracking (all are Copy types)");
            info!("=== Finished mem::forget handling ===");
            return;
        }

        // 第二步：检查所有需要 forget 的路径是否都可以 forget
        let mut invalid_paths = Vec::new();

        for path in &paths_to_forget {
            if !self
                .block_visitor
                .body_visitor
                .state
                .ownership_domain
                .can_forget(path)
            {
                let states = self
                    .block_visitor
                    .body_visitor
                    .state
                    .ownership_domain
                    .get_states(path);

                warn!(
                    "mem::forget - cannot forget path {:?}: invalid ownership state {:?}",
                    path, states
                );

                invalid_paths.push((path.clone(), states));
            }
        }

        // 如果有任何路径不能 forget，发出警告并跳过所有 forget 操作
        if !invalid_paths.is_empty() {
            let error_details: Vec<String> = invalid_paths
                .iter()
                .map(|(path, states)| format!("{:?} (states: {:?})", path, states))
                .collect();

            let warning = self
            .block_visitor
            .body_visitor
            .context
            .session
            .dcx()
            .struct_span_warn(
                self.block_visitor.body_visitor.current_span,
                format!(
                    "[Checker] Possible unsafe error: cannot forget values - invalid ownership states for {} path(s): [{}]",
                    invalid_paths.len(),
                    error_details.join(", ")
                ),
            );
            warning.emit();

            info!("mem::forget - operation aborted due to invalid ownership states");
            info!("=== Finished mem::forget handling ===");
            return;
        }

        // 第三步：所有路径都可以 forget，执行 forget 操作
        info!(
            "mem::forget - all {} paths can be forgotten, applying Forgotten state",
            paths_to_forget.len()
        );

        for path in &paths_to_forget {
            self.block_visitor
                .body_visitor
                .state
                .ownership_domain
                .add_state(path.clone(), OwnershipState::Forgotten);

            info!(
                "mem::forget - successfully added Forgotten state to path: {:?}",
                path
            );
        }

        info!(
            "mem::forget - successfully forgot {} path(s)",
            paths_to_forget.len()
        );
        info!("=== Finished mem::forget handling ===");
    }

    fn handle_manually_drop_new(&mut self) {
        assert!(self.actual_args.len() == 1);
        let arg_path = self.actual_args[0].0.clone();
        let arg_value = self.actual_args[0].1.clone();

        info!("=== Starting mem::ManuallyDrop::new handling ===");
        info!("ManuallyDrop::new - argument path: {:?}", arg_path);
        info!("ManuallyDrop::new - argument value: {:?}", arg_value);

        // 从参数符号值中提取实际的路径（可能有多个，如果是 Join）
        let actual_arg_paths = self.extract_path_from_ptr_value(&arg_value, &arg_path);

        info!(
            "ManuallyDrop::new - extracted argument paths: {:?}",
            actual_arg_paths
        );

        // 获取目标路径（返回值）
        let destination_path = self.block_visitor.get_path_for_place(&self.destination);
        info!(
            "ManuallyDrop::new - destination path: {:?}",
            destination_path
        );

        // 第一步：收集所有需要处理的路径
        let mut paths_to_process = Vec::new();

        for actual_arg_path in &actual_arg_paths {
            let needs_drop = self.needs_drop_for_path(actual_arg_path, false);
            info!(
                "ManuallyDrop::new - path {:?} needs_drop decision: {}",
                actual_arg_path, needs_drop
            );

            if needs_drop {
                paths_to_process.push(actual_arg_path.clone());
            }
        }

        // 如果没有需要处理的路径，直接返回
        if paths_to_process.is_empty() {
            info!("ManuallyDrop::new - no paths need ownership tracking (all are Copy types)");
            info!("=== Finished mem::ManuallyDrop::new handling ===");
            return;
        }

        // 第二步：检查所有路径是否都可以 move
        let mut invalid_paths = Vec::new();

        for path in &paths_to_process {
            if !self
                .block_visitor
                .body_visitor
                .state
                .ownership_domain
                .can_use(path)
            {
                let states = self
                    .block_visitor
                    .body_visitor
                    .state
                    .ownership_domain
                    .get_states(path);

                warn!(
                    "ManuallyDrop::new - cannot move path {:?}: invalid ownership state {:?}",
                    path, states
                );

                invalid_paths.push((path.clone(), states));
            }
        }

        // 如果有任何路径不能 move，发出警告并跳过所有操作
        if !invalid_paths.is_empty() {
            let error_details: Vec<String> = invalid_paths
                .iter()
                .map(|(path, states)| format!("{:?} (states: {:?})", path, states))
                .collect();

            let warning = self
            .block_visitor
            .body_visitor
            .context
            .session
            .dcx()
            .struct_span_warn(
                self.block_visitor.body_visitor.current_span,
                format!(
                    "[Checker] Possible unsafe error: cannot create ManuallyDrop - invalid ownership states for {} path(s): [{}]",
                    invalid_paths.len(),
                    error_details.join(", ")
                ),
            );
            warning.emit();

            info!("ManuallyDrop::new - operation aborted due to invalid ownership states");
            info!("=== Finished mem::ManuallyDrop::new handling ===");
            return;
        }

        // 第三步：所有路径都可以处理，执行 ManuallyDrop 操作
        info!(
            "ManuallyDrop::new - all {} paths can be moved into ManuallyDrop",
            paths_to_process.len()
        );

        // 将所有参数路径标记为 Moved（所有权已转移到 ManuallyDrop）
        for path in &paths_to_process {
            self.block_visitor
                .body_visitor
                .state
                .ownership_domain
                .add_state(path.clone(), OwnershipState::Moved);

            info!(
                "ManuallyDrop::new - marked argument path as Moved: {:?}",
                path
            );
        }

        // 目标路径（返回值）标记为 ManuallyManaged 状态
        self.block_visitor
            .body_visitor
            .state
            .ownership_domain
            .set_state(destination_path.clone(), OwnershipState::ManuallyManaged);

        info!(
            "ManuallyDrop::new - marked destination path as ManuallyManaged: {:?}",
            destination_path
        );

        info!(
            "ManuallyDrop::new - successfully processed {} path(s)",
            paths_to_process.len()
        );
        info!("=== Finished mem::ManuallyDrop::new handling ===");
    }

    // fn handle_write(&mut self) -> bool {
    //     assert!(self.actual_args.len() == 2);
    //     let dest_ptr_path = self.actual_args[0].0.clone();
    //     let dest_ptr_value = self.actual_args[0].1.clone();
    //     let src_val = self.actual_args[1].1.clone();

    //     info!("=== Starting ptr::write handling ===");
    //     info!("ptr::write - destination pointer path: {:?}", dest_ptr_path);
    //     info!("ptr::write - source value: {:?}", src_val);

    //     // 从指针符号值中提取实际的目标路径
    //     let dest_path = match &dest_ptr_value.expression {
    //         Expression::Reference(path) => Path::root(path),
    //         Expression::Variable { path, .. } => {
    //             let root = Path::root(path);
    //             Path::new_deref(root)
    //         }
    //         _ => {
    //             warn!("ptr::write - unexpected destination pointer value expression, creating deref path");
    //             Path::new_deref(Path::root(&dest_ptr_path))
    //         }
    //     };

    //     info!("ptr::write - extracted destination path: {:?}", dest_path);

    //     // 判断目标指针指向的类型是否需要 drop
    //     let needs_drop = self.needs_drop_for_path(&dest_ptr_path, true);
    //     info!("ptr::write - needs_drop check result: {}", needs_drop);

    //     if needs_drop {
    //         // 检查目标位置是否已有所有权状态（可能已有值）
    //         let dest_state = self
    //             .block_visitor
    //             .body_visitor
    //             .state
    //             .ownership_domain
    //             .get_state(&dest_path);

    //         info!("ptr::write - destination ownership state: {:?}", dest_state);

    //         // 如果目标位置已有值且处于 Owned 状态，覆盖写入会导致内存泄漏
    //         if matches!(*dest_state, OwnershipState::Owned) {
    //             warn!(
    //                 "ptr::write - writing to a location with owned value - potential memory leak"
    //             );
    //             let warning = self
    //                 .block_visitor
    //                 .body_visitor
    //                 .context
    //                 .session
    //                 .dcx()
    //                 .struct_span_warn(
    //                     self.block_visitor.body_visitor.current_span,
    //                     format!("[Checker] Possible unsafe error: ptr::write to a location with owned value (potential memory leak)"),
    //                 );
    //             warning.emit();
    //         }

    //         // 更新目标位置的所有权状态为 Owned
    //         self.block_visitor
    //             .body_visitor
    //             .state
    //             .ownership_domain
    //             .set_state(dest_path.clone(), Rc::new(OwnershipState::Owned));

    //         info!("ptr::write - updated destination ownership state to Owned");
    //     }

    //     info!("ptr::write - updating destination with source value");
    //     self.block_visitor
    //         .body_visitor
    //         .state
    //         .update_value_at(dest_path, src_val);

    //     info!("=== Finished ptr::write handling ===");
    //     true
    // }

    // fn handle_swap(&mut self) {}

    // fn handle_replace(&mut self) {}

    // 并在文件中添加这个独立函数
    fn emit_unsafe_error(
        check_result: CheckerResult,
        body_visitor: &mut BodyVisitor<'tcx, 'analysis, 'compilation, DomainType>,
        callee_def_id: DefId,
    ) {
        let vis = body_visitor.context.tcx.visibility(body_visitor.def_id);
        let vis_str = if vis.is_public() { "public" } else { "private" };

        let caller_is_unsafe = body_visitor
            .context
            .tcx
            .fn_sig(body_visitor.def_id)
            .skip_binder()
            .safety()
            .is_unsafe();
        info!("pub:{:?}, safety:{:?}", vis, caller_is_unsafe);
        // if !(vis_str == "public" && !caller_is_unsafe) {
        //     return;
        // }
        let caller_is_unsafe_str = if caller_is_unsafe { "unsafe" } else { "safe" };

        info!("body_visitor_def_id is {:?}", body_visitor.def_id);
        info!("callee_def_id is {:?}", callee_def_id);

        match check_result {
            CheckerResult::Safe => (),
            CheckerResult::Unsafe => {
                let error = body_visitor.context.session.dcx().struct_span_warn(
                    body_visitor.current_span,
                    format!(
                        "[Checker] Provably unsafe error: index out of bound in {:?} function {:?}",
                        caller_is_unsafe_str, vis_str
                    ),
                );
                error.emit();
            }
            CheckerResult::Warning => {
                let error = body_visitor.context.session.dcx().struct_span_warn(
                    body_visitor.current_span,
                    format!(
                        "[Checker] Possible unsafe error: index out of bound in {:?} function {:?}",
                        caller_is_unsafe_str, vis_str
                    ),
                );
                error.emit();
            }
        }
    }

    // _17(place) = index(move _18 move _19])
    fn handle_index(&mut self) {
        assert!(self.actual_args.len() == 2);
        #[allow(irrefutable_let_patterns)]
        let destination_path = if let dest = self.destination {
            Some(self.block_visitor.get_path_for_place(&dest))
        } else {
            None
        };
        assert!(destination_path.is_some());
        let state = self.block_visitor.state().clone();
        let body_visitor = &mut self.block_visitor.body_visitor;

        let array = &self.actual_args[0].0;

        // 在进行索引前检查底层数组/切片是否为 Uinit
        let array_states = body_visitor
            .state
            .ownership_domain
            .get_states(array);
        if array_states.contains(&OwnershipState::Uinit) {
            let warning = body_visitor
                .context
                .session
                .dcx()
                .struct_span_warn(
                    body_visitor.current_span,
                    "[Checker] Provably unsafe error: indexing into uninitialized array or slice",
                );
            warning.emit();
        }

        let array_len = Path::new_length(array.clone()).refine_paths(&body_visitor.state);
        let array_len_val = SymbolicValue::make_from(
            Expression::Variable {
                path: array_len.clone(),
                var_type: ExpressionType::Usize,
            },
            1,
        );
        let index_val = &self.actual_args[1].1;
        let result = destination_path.as_ref().unwrap();

        let assert_checker = AssertionChecker::new(body_visitor);
        let overflow_safe_cond = SymbolicValue::make_from(
            Expression::LessThan {
                left: index_val.clone(),
                right: array_len_val,
            },
            1,
        );
        // TODO:加上其他的验证条件
        let check_result = assert_checker.check_assert_condition(overflow_safe_cond, true, &state);

        match check_result {
            CheckerResult::Safe => (),
            CheckerResult::Unsafe => {
                // let error = body_visitor.context.session.dcx().struct_span_warn(
                //     body_visitor.current_span,
                //     format!("[Checker] Provably error: index out of bound",),
                // );
                // body_visitor.emit_diagnostic(error, false, DiagnosticCause::Index);
                // return;
            }
            CheckerResult::Warning => {
                // let warning = body_visitor.context.session.dcx().struct_span_warn(
                //     body_visitor.current_span,
                //     format!("[Checker] Possible error: index out of bound"),
                // );
                // body_visitor.emit_diagnostic(warning, false, DiagnosticCause::Index);
            }
        }

        let source =
            Path::new_index(array.clone(), index_val.clone()).refine_paths(&body_visitor.state);
        let ref_source = SymbolicValue::make_from(Expression::Reference(source).into(), 1);
        self.block_visitor
            .body_visitor
            .state
            .update_value_at(result.clone(), ref_source);
    }

    fn handle_from_utf8_unchecked(&self) {}

    /// Returns a list of (path, value) pairs where each path is rooted by an argument (or the result)
    /// or where the path root is a heap block reachable from an argument (or the result).
    /// Since paths are created by writes, these are side-effects.
    // OK
    fn extract_side_effects(
        &self,
        env: &AbstractDomain<DomainType>,
        argument_count: usize,
        offset: usize,
    ) -> Vec<(Rc<Path>, Rc<SymbolicValue>)> {
        let mut heap_roots: HashSet<Rc<SymbolicValue>> = HashSet::new();
        let mut result = Vec::new();
        for ordinal in 0..=argument_count {
            let root = if ordinal == 0 {
                Path::new_result()
            } else {
                Path::new_parameter(ordinal, offset)
            };

            // `path` is `result`, or `path` is rooted by `result` or parameters
            for path in env
                .get_paths_iter()
                .iter()
                .filter(|p| (ordinal == 0 && (**p) == root) || p.is_rooted_by(&root))
            {
                if let Some(value) = env.value_at(path) {
                    // Find and record heap roots in paths and values
                    // For Path, heap blocks are in `PathEnum::HeapBlock`
                    // For SymbolicValue, heap blocks are in `Expression::HeapBlock`
                    path.record_heap_blocks(&mut heap_roots);
                    value.record_heap_blocks(&mut heap_roots);
                    if let Expression::Variable { path: vpath, .. } = &value.expression {
                        if ordinal > 0 && vpath.eq(path) {
                            // The value is not an update, but just what was there at function entry.
                            // TODO: path=path, when will this happen?
                            continue;
                        }
                    }
                    // We are extracting a subset of information out of env, which has not overflowed.
                    result.push((path.clone(), value.clone()));
                }
            }
        }
        // Find path whose root is a heap block reachable from an argument (or the result)
        self.extract_reachable_heap_allocations(env, &mut heap_roots, &mut result);
        result
    }

    /// Adds roots for all new heap allocated objects that are reachable by the caller.
    /// This will modify `heap_roots` and `result`
    fn extract_reachable_heap_allocations(
        &self,
        env: &AbstractDomain<DomainType>,
        heap_roots: &mut HashSet<Rc<SymbolicValue>>,
        result: &mut Vec<(Rc<Path>, Rc<SymbolicValue>)>,
    ) {
        let mut visited_heap_roots: HashSet<Rc<SymbolicValue>> = HashSet::new();
        while heap_roots.len() > visited_heap_roots.len() {
            let mut new_roots: HashSet<Rc<SymbolicValue>> = HashSet::new();
            for heap_root in heap_roots.iter() {
                if visited_heap_roots.insert(heap_root.clone()) {
                    let root = Path::get_as_path(heap_root.clone());

                    for path in env
                        .get_paths_iter()
                        .iter()
                        // If path is a heap root or is rooted by a heap root
                        .filter(|p| (**p) == root || p.is_rooted_by(&root))
                    {
                        if let Some(value) = env.value_at(path) {
                            path.record_heap_blocks(&mut new_roots);
                            value.record_heap_blocks(&mut new_roots);
                            result.push((path.clone(), value.clone()));
                        }
                    }
                }
            }
            heap_roots.extend(new_roots.into_iter());
        }
    }

    /// Updates the current state to reflect the effects of a normal return from the function call.
    pub fn transfer_and_refine_normal_return_state(
        &mut self,
        function_post_state: &AbstractDomain<DomainType>,
        old_offset: usize,
    ) {
        debug!("Start to transfer and refine normal return state");
        #[allow(irrefutable_let_patterns)]
        let destination_path = if let dest = self.destination {
            Some(self.block_visitor.get_path_for_place(&dest))
        } else {
            None
        };

        if let Some(target_path) = &destination_path {
            debug!("target_path: {:?}", target_path);
            let return_value_path = Path::new_result();

            let side_effects =
                self.extract_side_effects(function_post_state, self.actual_args.len(), old_offset);

            debug!("side_effects: {:?}", side_effects);

            // Transfer side effects
            if !function_post_state.is_empty() {
                debug!("Handling side effects on call result");
                self.block_visitor.transfer_and_refine(
                    &side_effects,
                    target_path.clone(),
                    &return_value_path,
                    self.actual_args,
                );
            }
            // funtion_post_state is empty
            else {
                debug!("funtion_post_state is empty");
                let _result_type: ExpressionType = self
                    .block_visitor
                    .body_visitor
                    .type_visitor
                    .get_path_rustc_type(target_path, self.block_visitor.body_visitor.current_span)
                    .kind()
                    .into();

                let result = symbolic_value::TOP.into();
                debug!("Before updating top: {:?}", self.block_visitor.state());
                self.block_visitor
                    .body_visitor
                    .state
                    .update_value_at(return_value_path, result);
            }

            // 【新增逻辑】判断目标类型是否为引用或裸指针
            let target_type = self
                .block_visitor
                .body_visitor
                .type_visitor
                .get_path_rustc_type(target_path, self.block_visitor.body_visitor.current_span);

            let is_pointer_type =
                matches!(target_type.kind(), TyKind::Ref(..) | TyKind::RawPtr(..));

            info!(
                "path {:?} is ptr type: {:?} needs drop {:?}",
                target_path,
                is_pointer_type,
                self.needs_drop_for_path(target_path, false)
            );

            // 如果不是指针类型（引用或裸指针），说明是拥有所有权的变量
            // 并且该类型需要 drop，则初始化 ownership 域为 Owned 状态
            if !is_pointer_type && self.needs_drop_for_path(target_path, false) {
                info!(
                    "Initializing ownership for owned non-pointer type at path: {:?}",
                    target_path
                );

                // 更新 ownership 域为 Owned 状态
                let mut ownership_set: HashSet<OwnershipState> = HashSet::new();
                ownership_set.insert(OwnershipState::Owned);
                self.block_visitor
                    .body_visitor
                    .state
                    .ownership_domain
                    .state_map
                    .insert(target_path.clone(), ownership_set);

                info!("Successfully initialized ownership state to Owned");
            }
        }
    }
}
