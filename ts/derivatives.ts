// Copyright Crispin Perdue.  All rights reserved.
//

namespace Toy {

  // Let's say that "drv" is a function of a function of
  // an individual that yields a function of an individual
  // that yields the (real) value of the derivative
  // of the input function when given a real number
  // and nil (none) for any other input.
  declare(
    // {definition: 'RR f == forall {x. R x => R (f x)}'},

    // {definition: 'fun f == exists {y. y = f x}'},

    // X is "defined".
    {definition: 'def x == x != none'},

    // Restriction of the range of a function
    {definition: 'f @@ p = {x. if (p (f x)) (f x) none}'},

    // True when f is "defined" only for inputs in p.
    {definition: 'f mapsFrom p == forall {x. def (f x) => p x}'},

    // True when all "defined" outputs of f are in p.
    {definition: 'f mapsTo p == forall {x. def (f x) => p (f x)}'},

    // Fact about domain restriction.
    {statement: 'f @ p mapsFrom p'},

    {definition: 'mapping d c f == f mapsFrom d & f mapsTo c'},
    {definition: 'RRfun f == mapping R R f'},
    {statement: 'mapping R R f => RRfun (drv f)'},
    // {statement: 'RRfun (drv (f @ R @@ R))'},
    // {statement: 'f @ R mapsTo R => RRfun (drv (f @ R))'},

    // True when f1 (restricted to real inputs and outputs) is
    // the derivative of f (restricted to real inputs and outputs).
    {definition: 'realDrv f f1 == drv (f @ R @@ R) = f1 @ R @@ R'},

    // Real numbers plus "none".
    {definition: 'Rz = {x. R x | R = none}'},

    {statement: 'drv (f @ R) mapsTo R'},
    {statement: 'drv f x in Rz'},

    // Identity function
    {statement:
      'realDrv {x. x} {x. 1}',
    },
    // Constant function
    {statement:
      'realDrv {x. k} (if (R k) {x. 0} {x. none})',
    },
    {statement:
      'realdrv {x. x ** n}  {x. R x & R n ?? n * x ** (n - 1)}',
    },
    // f and g differentiable at x!!
    {statement:
      'd = drv f x + drv g x => drv {y. f y + g y} x = d',
    },
    {statement:
      'd = drv f x - drv g x => drv {y. f y - g y} x = d',
    },
    {statement:
      'd = drv f x * g x + drv g x * f x => drv {x. f x * g x} x = d',
    },
    {statement: 
     `d = (drv f x * g x - drv g x * f x) / (g x) ** 2 =>
        drv {x. f x / g x} x = d`,
    },
    {statement:
      'd = drv f (g x) * drv g x => drv {x. (f (g x))} x = d',
    },
  );

  /*
    {statement:
      'dffrbl f & dffrbl g => dffrbl {x. g (f x)}',
    },
  );
  */

}
