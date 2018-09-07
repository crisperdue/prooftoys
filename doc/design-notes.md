## Bound variable (re)naming in rewrite rules

Mathtoys rewriting propagates names of bound variables from the input
step to the result using higher-order matching together with renaming
of bound variables in certain cases.

The result of a higher-order match retains the exact content of the
part of the input step matching the schema. All of the variable names
then appear in the results of substitutions, though occurrences free
in the input may become bound in the result since the input is wrapped
in one or more lamba terms in matching it against a function variable.

When Mathtoys higher-order matching wraps a source term in n layers of
lambdas, it records n in the %expansions map, keyed by the name of the
free variable.  Performing that many beta reductions results in the
matched part of the input step.

In a rewrite rule RHS, an LHS function variable may occur with one or
more arguments, and each is typically a bound variable.  When a lambda
term applied to a variable, beta reduction renames the inner bound
variable to have the name of the outer variable, removing the lambda.
If the outer variable is a bound variable, Mathtoys first renames the
outer variable to have the same name as the inner one.  In this case
the substitution leaves the body of the inner lambda unchanged,
removing the inner lambda.  This propagates bound variable names from
the input step to the output step.






