// You thought addition is easy?
// How about an add function whose arguments can alias :)?
module PulseAdd

#lang-pulse

open Pulse.Lib.Pervasives
open FStar.UInt64
open Pulse.Lib.Trade

module U64 = FStar.UInt64
module TU = Pulse.Lib.Trade.Util

fn add (x y: ref U64.t) (#c: slprop)
  // requires pts_to y 'y ** (pts_to y 'y ==>* (pts_to x 'x ** c))
  requires pts_to y 'y ** (pts_to y 'y @==> (pts_to x 'x ** c))
  ensures  pts_to x ('x +%^ 'y) ** c
{
  let b = !y;
  elim_trade (pts_to y 'y) (pts_to x 'x ** c);
  let a = !x;
  x := a +%^ b;
}

fn test_add_alias()
{
  let mut x : U64.t = 1234uL;

  // constructing: (x -> !x) |- (x -> !x)
  TU.refl (pts_to x !x);
  // constructing: (x -> !x) |- (x -> !x) ** emp
  TU.weak_concl_r (pts_to x !x) (pts_to x !x) emp;

  add x x;
}

fn test_add_non_alias()
{
  let mut x : U64.t = 1234uL;
  let mut y : U64.t = 5678uL;

  // constructing: (y -> !y) |- (y -> !y)
  TU.refl (pts_to y !y);
  // constructing: (y -> !y) |- (x -> !x) ** (y -> !y)
  TU.weak_concl_l (pts_to y !y) (pts_to y !y) (pts_to x !x);

  add x y;
}
