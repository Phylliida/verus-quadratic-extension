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
//   RuntimeQExtRat — runtime quadratic extension over rationals
//  ═══════════════════════════════════════════════════════════════════

///  Runtime element of the quadratic extension Q(sqrt(d)).
///
///  Represents re + im * sqrt(d) where d is determined by R.
///  The radicand type R is zero-sized (Sqrt2, Sqrt3, etc.) and
///  only exists at the type level.
///
///  Follows the same Ghost model pattern as RuntimeVec2/RuntimeVec3
///  in verus-linalg.
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
    ///  Well-formedness: runtime components match the ghost model.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.re.wf_spec()
        &&& self.im.wf_spec()
        &&& self.re@ == self@.re
        &&& self.im@ == self@.im
    }

    ///  Construct from two RuntimeRationals.
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

    ///  Construct the zero element: 0 + 0 * sqrt(d).
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

    ///  Construct the one element: 1 + 0 * sqrt(d).
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

    ///  Construct from an integer (embeds as re + 0 * sqrt(d)).
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

    //  ───────────────────────────────────────────────────────────────
    //  Algebraic operations
    //  ───────────────────────────────────────────────────────────────

    ///  Addition: (a + b*sqrt(d)) + (c + e*sqrt(d)) = (a+c) + (b+e)*sqrt(d)
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

    ///  Subtraction: (a + b*sqrt(d)) - (c + e*sqrt(d)) = (a-c) + (b-e)*sqrt(d)
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

    ///  Negation: -(a + b*sqrt(d)) = (-a) + (-b)*sqrt(d)
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

    ///  Multiplication: (a + b*sqrt(d)) * (c + e*sqrt(d))
    ///                = (a*c + b*e*d) + (a*e + b*c)*sqrt(d)
    ///
    ///  Requires a RuntimeRadicand witness to obtain the radicand value at runtime.
    pub fn mul_exec<RR: RuntimeRadicand<R>>(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == qe_mul::<Rational, R>(self@, rhs@),
    {
        let d_rt = RR::exec_value();

        //  Real part: a*c + b*e*d
        let ac = self.re.mul(&rhs.re);
        let be = self.im.mul(&rhs.im);
        let bed = be.mul(&d_rt);
        let re = ac.add(&bed);

        //  Imaginary part: a*e + b*c
        let ae = self.re.mul(&rhs.im);
        let bc = self.im.mul(&rhs.re);
        let im = ae.add(&bc);

        let ghost model = qe_mul::<Rational, R>(self@, rhs@);
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    ///  Conjugate: (a + b*sqrt(d)) -> (a - b*sqrt(d))
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

    ///  Component-wise equivalence check: a.re == b.re && a.im == b.im.
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

    ///  Copy by copying internal witnesses.
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

    ///  Norm: a^2 - b^2*d (an element of the base field, not of the extension).
    ///
    ///  Requires a RuntimeRadicand witness to obtain the radicand value at runtime.
    pub fn norm_exec<RR: RuntimeRadicand<R>>(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == qe_norm::<Rational, R>(self@),
    {
        let d_rt = RR::exec_value();

        //  a^2
        let a_sq = self.re.mul(&self.re);
        //  b^2
        let b_sq = self.im.mul(&self.im);
        //  b^2 * d
        let b_sq_d = b_sq.mul(&d_rt);
        //  a^2 - b^2*d
        a_sq.sub(&b_sq_d)
    }

    ///  Reciprocal: (a + b√d)⁻¹ = (a - b√d) / (a² - b²d)
    ///            = (a·n⁻¹) + (-b·n⁻¹)√d  where n = a² - b²d.
    ///
    ///  Requires self ≢ 0 (otherwise norm would be 0).
    pub fn recip_exec<RR: RuntimeRadicand<R>>(&self) -> (out: Self)
        requires
            self.wf_spec(),
            !qe_eqv::<Rational, R>(self@, qe_zero::<Rational, R>()),
        ensures
            out.wf_spec(),
            out@ == qe_recip::<Rational, R>(self@),
    {
        //  Compute norm = a² - b²d
        let norm = self.norm_exec::<RR>();

        //  Prove norm ≠ 0 via lemma_norm_nonzero
        proof {
            crate::lemmas::lemma_norm_nonzero::<Rational, R>(self@);
        }

        //  Get norm⁻¹
        let norm_inv = norm.recip().unwrap();

        //  re_out = a * norm⁻¹
        let re = self.re.mul(&norm_inv);
        //  im_out = (-b) * norm⁻¹
        let neg_im = self.im.neg();
        let im = neg_im.mul(&norm_inv);

        let ghost model = qe_recip::<Rational, R>(self@);
        RuntimeQExtRat { re, im, model: Ghost(model) }
    }

    ///  Division: x / y = x * y⁻¹.
    ///
    ///  Requires y ≢ 0.
    pub fn div_exec<RR: RuntimeRadicand<R>>(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            !qe_eqv::<Rational, R>(rhs@, qe_zero::<Rational, R>()),
        ensures
            out.wf_spec(),
            out@ == qe_div::<Rational, R>(self@, rhs@),
    {
        let rhs_inv = rhs.recip_exec::<RR>();
        self.mul_exec::<RR>(&rhs_inv)
    }
}

//  ═══════════════════════════════════════════════════════════════════
//   Ordering operations (require PositiveRadicand)
//  ═══════════════════════════════════════════════════════════════════

impl<R: PositiveRadicand<Rational>> RuntimeQExtRat<R> {
    ///  Non-negativity check: a + b√d ≥ 0.
    ///
    ///  Evaluates the 3-case predicate from qe_nonneg:
    ///  1. a ≥ 0 and b ≥ 0
    ///  2. a ≥ 0, b < 0, b²d ≤ a²
    ///  3. a < 0, b > 0, a² ≤ b²d
    pub fn nonneg_exec<RR: RuntimeRadicand<R>>(&self) -> (out: bool)
        requires
            self.wf_spec(),
        ensures
            out == qe_nonneg::<Rational, R>(self@),
    {
        let zero = RuntimeRational::from_int(0);

        let a_nonneg = zero.le(&self.re);   //  0 ≤ a
        let b_nonneg = zero.le(&self.im);   //  0 ≤ b

        if a_nonneg && b_nonneg {
            //  Case 1: both non-negative
            return true;
        }

        //  Compute a² and b²d for cases 2 and 3
        let a_sq = self.re.mul(&self.re);
        let b_sq = self.im.mul(&self.im);
        let d_rt = RR::exec_value();
        let b2d = b_sq.mul(&d_rt);

        let b_neg = self.im.lt(&zero);      //  b < 0
        let a_neg = self.re.lt(&zero);       //  a < 0
        let b_pos = zero.lt(&self.im);       //  0 < b

        if a_nonneg && b_neg && b2d.le(&a_sq) {
            //  Case 2: a ≥ 0, b < 0, b²d ≤ a²
            return true;
        }

        if a_neg && b_pos && a_sq.le(&b2d) {
            //  Case 3: a < 0, b > 0, a² ≤ b²d
            return true;
        }

        false
    }

    ///  Less-than-or-equal: x ≤ y iff y - x ≥ 0.
    pub fn le_exec<RR: RuntimeRadicand<R>>(&self, rhs: &Self) -> (out: bool)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out == qe_le::<Rational, R>(self@, rhs@),
    {
        let diff = rhs.sub_exec(self);
        diff.nonneg_exec::<RR>()
    }

    ///  Strict less-than: x < y iff x ≤ y and x ≢ y.
    pub fn lt_exec<RR: RuntimeRadicand<R>>(&self, rhs: &Self) -> (out: bool)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out == qe_lt::<Rational, R>(self@, rhs@),
    {
        let le = self.le_exec::<RR>(rhs);
        let eq = self.eq_exec(rhs);
        le && !eq
    }
}

} //  verus!
