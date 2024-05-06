use core::fmt::Debug;
use std::fmt::Display;
use std::{
    hash::Hash,
    ops::{Add, Div, Mul, Sub},
};

pub trait Field:
    Copy + Clone + Debug + Eq + Add<Output = Self> + Mul<Output = Self> + Sub<Output = Self> + Hash
{
    const ZERO: Self;
    const ONE: Self;
    const TWO: Self;
    const MONE: Self;
    fn add(self, _: Self) -> Self;
    fn mul(self, _: Self) -> Self;
    fn div(self, _: Self) -> Self;
    fn from_u32(i: u32) -> Self;
    fn to_u32(self) -> u32;
}

impl Field for i32 {
    const ZERO: Self = 0;
    const ONE: Self = 1;
    const TWO: Self = 2;
    const MONE: Self = -1;
    fn add(self, rhs: Self) -> Self {
        self + rhs
    }
    fn mul(self, rhs: Self) -> Self {
        self * rhs
    }
    fn div(self, rhs: Self) -> Self {
        self / rhs
    }
    fn from_u32(i: u32) -> Self {
        i.try_into().unwrap()
    }
    fn to_u32(self) -> u32 {
        self.try_into().unwrap()
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Fi64(pub i64);

impl Display for Fi64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}

impl Add for Fi64 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        <Self as Field>::add(self, rhs)
    }
}

impl Sub for Fi64 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        <Self as Field>::add(self, Field::mul(rhs, Field::MONE))
    }
}

impl Mul for Fi64 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        <Self as Field>::mul(self, rhs)
    }
}

impl Div for Fi64 {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        <Self as Field>::div(self, rhs)
    }
}

impl Field for Fi64 {
    const ZERO: Self = Fi64(0);
    const ONE: Self = Fi64(1);
    const TWO: Self = Fi64(2);
    const MONE: Self = Fi64(-1);
    fn add(self, rhs: Self) -> Self {
        Fi64(self.0.wrapping_add(rhs.0))
    }
    fn mul(self, rhs: Self) -> Self {
        Fi64(self.0.wrapping_mul(rhs.0))
    }
    fn div(self, rhs: Self) -> Self {
        Fi64(self.0.wrapping_div(rhs.0))
    }
    fn from_u32(i: u32) -> Self {
        Fi64(i.into())
    }
    fn to_u32(self) -> u32 {
        self.0.try_into().unwrap()
    }
}
