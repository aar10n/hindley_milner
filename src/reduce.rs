use crate::Context;

use std::ops::{ControlFlow, FromResidual, Try};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepResult<T> {
    /// The item was reduced.
    Reduced(T),
    /// The reduction is done.
    Done(T),
}

impl<T> StepResult<T> {
    pub fn to_pair(self) -> (T, bool) {
        match self {
            StepResult::Reduced(t) => (t, true),
            StepResult::Done(t) => (t, false),
        }
    }

    pub fn unwrap(self) -> T {
        match self {
            StepResult::Reduced(t) => t,
            StepResult::Done(t) => t,
        }
    }

    pub fn is_done(&self) -> bool {
        match self {
            StepResult::Reduced(_) => false,
            StepResult::Done(_) => true,
        }
    }
}

impl<T> Try for StepResult<T> {
    type Output = T;
    type Residual = T;

    fn from_output(output: Self::Output) -> Self {
        StepResult::Reduced(output)
    }

    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            StepResult::Reduced(t) => ControlFlow::Break(t),
            StepResult::Done(t) => ControlFlow::Continue(t),
        }
    }
}

impl<T> FromResidual for StepResult<T> {
    fn from_residual(residual: T) -> Self {
        StepResult::Reduced(residual)
    }
}

pub fn each_step<T>(
    ctx: &Context,
    t: T,
    reduce_fn: impl FnOnce(&Context, T) -> (T, bool) + Copy,
    mut step_fn: impl FnMut(&Context, &T) -> (),
) -> T {
    let mut t = t;
    for _ in 0..20 {
        let (u, c) = reduce_fn(ctx, t);
        t = u;

        step_fn(ctx, &t);
        if !c {
            break;
        }
    }
    t
}
