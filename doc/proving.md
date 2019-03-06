## Building proofs with Mathtoys

Mathematical reasoning is based on rules.  The rules describe what you
can correctly deduce from mathematical statements that are already
known to be true.

Using just a handful of rules for mathematical reasoning, you can
build proofs with Mathtoys.  Most of these rules work with two steps
and produce a third step as a consequence of the two inputs.

Some rules need an equation as one input.  The equation may equate
ordinary values such as numbers, as in an equation such as x + y = y +
x.  It may equate truth values, as in T == not F.  In fact it may
equate values of any kind handled by Mathtoys.

Other rules work with any statement already known to be true, and do
not require that the statement has the form of an equation.

Either way, the equation or proved fact can be one that is true, but
under certain conditions.  The rules still work, with the conditions
of both steps combined.

### Mathtoys concepts

#### Values

Mathtoys starts with boolean values (true and false written as T and
F), and individuals such as numbers, which you may enter as integers
with an optional minus sign.  Beyond this, given any two types,
functions from one to the other also constitute a type.  This results
in types for concepts found in most of mathematics, Including the
usual predicates, sets, and relations.

The boolean operator "not", for example, is a function that maps from
a boolean value to a boolean value.  The boolean operator "and" maps
from a pair of boolean values to a boolean value.  The function that
maps a number x to x*x maps from individuals (specifically numbers) to
individuals.

A set of numbers is a function from individuals to booleans.  A
sequence of numbers is a function from individuals to integers
(individuals), and so on.

#### Constants and variables

Variable names are a letter, optionally followed by an underscore and
one or more digits.  Any digits display as a subscript on the
identifier.  The names "T", "F", "R", and "e" are specially reserved
for constants.

Aside from the reserved special names, a constant is named by an
identifier, or by a sequence of printing (currently ASCII) characters
not including any alphanumerics, brackets, braces, parentheses, or
"-".  Identifiers begin with an alphabetic character which must be
followed by at least one alphanumeric.

#### Expressions (terms)

Everything in Mathtoys is an individual, such as a number, a boolean,
or a function.  Functions with boolean values are usually known as
predicates and relations.

Mathtoys has variables of all types, including functions and
relations.  You do not write down the types, but it parses expressions
into terms, and each term has a type.

#### Reasoning

Substitution

Replacement

Reduction (advanced)

### Starting out

#### Assuming a statement

#### Considering a term

#### Tautologies

### Rewriting

#### Rewriting using an equation

#### Rewriting without an equation

### Working with assumptions

### Higher-order matching

### Special cases

R5239 and R5239a

