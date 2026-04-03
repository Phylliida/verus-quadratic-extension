use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;
#[cfg(verus_keep_ghost)]
use crate::radicand::Radicand;
#[cfg(verus_keep_ghost)]
use crate::radicand::PositiveRadicand;
#[cfg(verus_keep_ghost)]
use crate::spec::*;
#[cfg(verus_keep_ghost)]
use crate::ordered::*;
#[cfg(verus_keep_ghost)]
use crate::instances::*;

#[cfg(verus_keep_ghost)]
verus! {

///  The scalar model type: verified rational numbers.
pub type RationalModel = Rational;

//  ═══════════════════════════════════════════════════════════════════
//   RuntimeRadicand trait — provides exec-level radicand value
//  ═══════════════════════════════════════════════════════════════════

///  Trait for obtaining the runtime value of a radicand.
///
///  Each concrete radicand type (Sqrt2, Sqrt3, Sqrt5) implements this
///  to provide its integer value as a RuntimeRational.
pub trait RuntimeRadicand<R: Radicand<Rational>>: Sized {
    fn exec_value() -> (out: RuntimeRational)
        ensures
            out.wf_spec(),
            out@ == R::value(),
    ;
}

//  ── Concrete RuntimeRadicand implementations ──────────────────────

pub struct RuntimeSqrt2;

impl RuntimeRadicand<Sqrt2> for RuntimeSqrt2 {
    fn exec_value() -> (out: RuntimeRational)
        ensures
            out.wf_spec(),
            out@ == Sqrt2::value(),
    {
        RuntimeRational::from_int(2)
    }
}

pub struct RuntimeSqrt3;

impl RuntimeRadicand<Sqrt3> for RuntimeSqrt3 {
    fn exec_value() -> (out: RuntimeRational)
        ensures
            out.wf_spec(),
            out@ == Sqrt3::value(),
    {
        RuntimeRational::from_int(3)
    }
}

pub struct RuntimeSqrt5;

impl RuntimeRadicand<Sqrt5> for RuntimeSqrt5 {
    fn exec_value() -> (out: RuntimeRational)
        ensures
            out.wf_spec(),
            out@ == Sqrt5::value(),
    {
        RuntimeRational::from_int(5)
    }
}

pub struct RuntimeSqrt6;

impl RuntimeRadicand<Sqrt6> for RuntimeSqrt6 {
    fn exec_value() -> (out: RuntimeRational)
        ensures
            out.wf_spec(),
            out@ == Sqrt6::value(),
    {
        RuntimeRational::from_int(6)
    }
}

pub struct RuntimeSqrt7;

impl RuntimeRadicand<Sqrt7> for RuntimeSqrt7 {
    fn exec_value() -> (out: RuntimeRational)
        ensures
            out.wf_spec(),
            out@ == Sqrt7::value(),
    {
        RuntimeRational::from_int(7)
    }
}

pub struct RuntimeSqrt10;

impl RuntimeRadicand<Sqrt10> for RuntimeSqrt10 {
    fn exec_value() -> (out: RuntimeRational)
        ensures
            out.wf_spec(),
            out@ == Sqrt10::value(),
    {
        RuntimeRational::from_int(10)
    }
}

pub struct RuntimeSqrt11;

impl RuntimeRadicand<Sqrt11> for RuntimeSqrt11 {
    fn exec_value() -> (out: RuntimeRational)
        ensures
            out.wf_spec(),
            out@ == Sqrt11::value(),
    {
        RuntimeRational::from_int(11)
    }
}

pub struct RuntimeSqrt13;

impl RuntimeRadicand<Sqrt13> for RuntimeSqrt13 {
    fn exec_value() -> (out: RuntimeRational)
        ensures
            out.wf_spec(),
            out@ == Sqrt13::value(),
    {
        RuntimeRational::from_int(13)
    }
}

//  ═══════════════════════════════════════════════════════════════════
//   Copy helper
//  ═══════════════════════════════════════════════════════════════════

///  Copy a RuntimeRational by copying its internal witnesses.
pub fn copy_rational(r: &RuntimeRational) -> (out: RuntimeRational)
    requires
        r.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == r@,
{
    let num_copy = r.numerator.copy_small_total();
    let den_copy = r.denominator.copy_small_total();
    RuntimeRational {
        numerator: num_copy,
        denominator: den_copy,
        model: Ghost(r@),
    }
}

//  ═══════════════════════════════════════════════════════════════════
//   RuntimeQExtRat — type alias for generic RuntimeQExt over Rational
//  ═══════════════════════════════════════════════════════════════════

///  Runtime element of Q(√d), now a type alias for the generic RuntimeQExt.
///
///  Migration note: Previously a standalone struct. Now delegates to
///  RuntimeQExt<Rational, R, RuntimeRational> which stores the radicand
///  value in the struct and routes all ops through RuntimeRingOps (canonical).
pub type RuntimeQExtRat<R> = crate::runtime_qext::RuntimeQExtL1<R>;

} //  verus!
