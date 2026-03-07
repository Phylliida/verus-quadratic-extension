use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;
#[cfg(verus_keep_ghost)]
use crate::radicand::Radicand;
#[cfg(verus_keep_ghost)]
use crate::spec::*;
#[cfg(verus_keep_ghost)]
use crate::instances::*;

#[cfg(verus_keep_ghost)]
verus! {

/// The scalar model type: verified rational numbers.
pub type RationalModel = Rational;

// ═══════════════════════════════════════════════════════════════════
//  RuntimeRadicand trait — provides exec-level radicand value
// ═══════════════════════════════════════════════════════════════════

/// Trait for obtaining the runtime value of a radicand.
///
/// Each concrete radicand type (Sqrt2, Sqrt3, Sqrt5) implements this
/// to provide its integer value as a RuntimeRational.
pub trait RuntimeRadicand<R: Radicand<Rational>>: Sized {
    fn exec_value() -> (out: RuntimeRational)
        ensures
            out.wf_spec(),
            out@ == R::value(),
    ;
}

// ── Concrete RuntimeRadicand implementations ──────────────────────

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

// ═══════════════════════════════════════════════════════════════════
//  Copy helper
// ═══════════════════════════════════════════════════════════════════

/// Copy a RuntimeRational by copying its internal witnesses.
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

// ═══════════════════════════════════════════════════════════════════
//  RuntimeQExtRat — runtime quadratic extension over rationals
// ═══════════════════════════════════════════════════════════════════

/// Runtime element of the quadratic extension Q(sqrt(d)).
///
/// Represents re + im * sqrt(d) where d is determined by R.
/// The radicand type R is zero-sized (Sqrt2, Sqrt3, etc.) and
/// only exists at the type level.
///
/// Follows the same Ghost model pattern as RuntimeVec2/RuntimeVec3
/// in verus-linalg.
pub struct RuntimeQExtRat<R: Radicand<Rational>> {
    pub re: RuntimeRational,
    pub im: RuntimeRational,
    pub model: Ghost<SpecQuadExt<Rational, R>>,
}

impl<R: Radicand<Rational>> View for RuntimeQExtRat<R> {
    type V = SpecQuadExt<Rational, R>;

    open spec fn view(&self) -> SpecQuadExt<Rational, R> {
        self.model@
    }
}

impl<R: Radicand<Rational>> RuntimeQExtRat<R> {
    /// Well-formedness: runtime components match the ghost model.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.re.wf_spec()
        &&& self.im.wf_spec()
        &&& self.re@ == self@.re
        &&& self.im@ == self@.im
    }

    /// Construct from two RuntimeRationals.
    pub fn new(re: RuntimeRational, im: RuntimeRational) -> (out: Self)
        requires
            re.wf_spec(),
            im.wf_spec(),
        ensures
            out.wf_spec(),
            out@.re == re@,
            out@.im == im@,
    {
        let ghost model = qext::<Rational, R>(re@, im@);
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    /// Construct the zero element: 0 + 0 * sqrt(d).
    pub fn zero_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == qe_zero::<Rational, R>(),
    {
        let re = RuntimeRational::from_int(0);
        let im = RuntimeRational::from_int(0);
        let ghost model = qe_zero::<Rational, R>();
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    /// Construct the one element: 1 + 0 * sqrt(d).
    pub fn one_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == qe_one::<Rational, R>(),
    {
        let re = RuntimeRational::from_int(1);
        let im = RuntimeRational::from_int(0);
        let ghost model = qe_one::<Rational, R>();
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    /// Construct from an integer (embeds as re + 0 * sqrt(d)).
    pub fn from_int(value: i64) -> (out: Self)
        ensures
            out.wf_spec(),
            out@.re == Rational::from_int_spec(value as int),
            out@.im == Rational::from_int_spec(0),
    {
        let re = RuntimeRational::from_int(value);
        let im = RuntimeRational::from_int(0);
        let ghost model = qext::<Rational, R>(
            Rational::from_int_spec(value as int),
            Rational::from_int_spec(0),
        );
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    // ───────────────────────────────────────────────────────────────
    // Algebraic operations
    // ───────────────────────────────────────────────────────────────

    /// Addition: (a + b*sqrt(d)) + (c + e*sqrt(d)) = (a+c) + (b+e)*sqrt(d)
    pub fn add_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == qe_add::<Rational, R>(self@, rhs@),
    {
        let re = self.re.add(&rhs.re);
        let im = self.im.add(&rhs.im);
        let ghost model = qe_add::<Rational, R>(self@, rhs@);
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    /// Subtraction: (a + b*sqrt(d)) - (c + e*sqrt(d)) = (a-c) + (b-e)*sqrt(d)
    pub fn sub_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == qe_sub::<Rational, R>(self@, rhs@),
    {
        let re = self.re.sub(&rhs.re);
        let im = self.im.sub(&rhs.im);
        let ghost model = qe_sub::<Rational, R>(self@, rhs@);
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    /// Negation: -(a + b*sqrt(d)) = (-a) + (-b)*sqrt(d)
    pub fn neg_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == qe_neg::<Rational, R>(self@),
    {
        let re = self.re.neg();
        let im = self.im.neg();
        let ghost model = qe_neg::<Rational, R>(self@);
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    /// Multiplication: (a + b*sqrt(d)) * (c + e*sqrt(d))
    ///               = (a*c + b*e*d) + (a*e + b*c)*sqrt(d)
    ///
    /// Requires a RuntimeRadicand witness to obtain the radicand value at runtime.
    pub fn mul_exec<RR: RuntimeRadicand<R>>(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == qe_mul::<Rational, R>(self@, rhs@),
    {
        let d_rt = RR::exec_value();

        // Real part: a*c + b*e*d
        let ac = self.re.mul(&rhs.re);
        let be = self.im.mul(&rhs.im);
        let bed = be.mul(&d_rt);
        let re = ac.add(&bed);

        // Imaginary part: a*e + b*c
        let ae = self.re.mul(&rhs.im);
        let bc = self.im.mul(&rhs.re);
        let im = ae.add(&bc);

        let ghost model = qe_mul::<Rational, R>(self@, rhs@);
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    /// Conjugate: (a + b*sqrt(d)) -> (a - b*sqrt(d))
    pub fn conj_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == qe_conj::<Rational, R>(self@),
    {
        let re = copy_rational(&self.re);
        let im = self.im.neg();
        let ghost model = qe_conj::<Rational, R>(self@);
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    /// Component-wise equivalence check: a.re == b.re && a.im == b.im.
    pub fn eq_exec(&self, rhs: &Self) -> (out: bool)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out == qe_eqv::<Rational, R>(self@, rhs@),
    {
        let re_eq = self.re.eq(&rhs.re);
        let im_eq = self.im.eq(&rhs.im);
        re_eq && im_eq
    }

    /// Copy by copying internal witnesses.
    pub fn copy_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@,
    {
        let re = copy_rational(&self.re);
        let im = copy_rational(&self.im);
        RuntimeQExtRat { re, im, model: Ghost(self@) }
    }

    /// Norm: a^2 - b^2*d (an element of the base field, not of the extension).
    ///
    /// Requires a RuntimeRadicand witness to obtain the radicand value at runtime.
    pub fn norm_exec<RR: RuntimeRadicand<R>>(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == qe_norm::<Rational, R>(self@),
    {
        let d_rt = RR::exec_value();

        // a^2
        let a_sq = self.re.mul(&self.re);
        // b^2
        let b_sq = self.im.mul(&self.im);
        // b^2 * d
        let b_sq_d = b_sq.mul(&d_rt);
        // a^2 - b^2*d
        a_sq.sub(&b_sq_d)
    }
}

} // verus!
