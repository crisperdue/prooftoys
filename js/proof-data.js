Toy.proofData =
[
 {
  "doc": "/equations/",
  "proof": [
   "(1 consider (t (((4 * ((2 * x) - 3)) + 7) = ((3 * x) + 5))))",
   "(2 rewrite (s 1) (path \"/main/right/left/left\") (t ((((R a) & (R b)) & (R c)) => ((a * (b - c)) = ((a * b) - (a * c))))))",
   "(3 simplifyProducts (s 2) (path \"/main/right/left/left\"))",
   "(4 simplifySite (s 3) (path \"/right/right\"))",
   "(5 addThisToBoth (s 4) (path \"/right/right/left/right\"))",
   "(6 simplifySums (s 5) (path \"/right/right\"))",
   "(7 subtractThisFromBoth (s 6) (path \"/right/right/right/left\"))",
   "(8 simplifySums (s 7) (path \"/right/right\"))",
   "(9 rewrite (s 8) (path \"/right/right/left\") (t ((((R a) & (R b)) & (R c)) => (((a * c) - (b * c)) = ((a - b) * c)))))",
   "(10 simplifyFocalPart (s 9))",
   "(11 divideBothByThis (s 10) (path \"/right/right/left/left\"))",
   "(12 simplifyProducts (s 11) (path \"/right/right\"))"
  ]
 },
 {
  "doc": "/equations/#2",
  "proof": [
   "(1 consider (t ((8 * (2 - t)) = (-5 * t))))",
   "(2 rewrite (s 1) (path \"/main/right/left\") (t ((((R a) & (R b)) & (R c)) => ((a * (b - c)) = ((a * b) - (a * c))))))",
   "(3 simplifyProducts (s 2) (path \"/main/right/left\"))",
   "(4 addThisToBoth (s 3) (path \"/right/right/left/right\"))",
   "(5 simplifySums (s 4) (path \"/right/right\"))",
   "(6 rewrite (s 5) (path \"/right/right/right\") (t ((((R a) & (R b)) & (R c)) => (((a * c) + (b * c)) = ((a + b) * c)))))",
   "(7 simplifyFocalPart (s 6))",
   "(8 rewrite (s 7) (path \"/right/right/left/left\") (t (((R x) & (R y)) => ((x + y) = (y + x)))))",
   "(9 simplifyFocalPart (s 8))",
   "(10 rewrite (s 9) (path \"/right/right\") (t ((x = y) == (y = x))))",
   "(11 divideBothByThis (s 10) (path \"/right/right/left/left\"))",
   "(12 simplifyProducts (s 11) (path \"/right/right\"))"
  ]
 },
 {
  "doc": "/equations/#3",
  "proof": [
   "(1 consider (t (((5 * x) - 6) = (2 / 3))))",
   "(2 addThisToBoth (s 1) (path \"/main/right/left/right\"))",
   "(3 simplifySums (s 2) (path \"/right/right\"))",
   "(4 rewrite (s 3) (path \"/right/right/right\") (t ((((R b) & (R c)) & (c != 0)) => (((a / c) + b) = ((a / c) + ((b * c) / c))))))",
   "(5 rewrite (s 4) (path \"/right/right/right/right\") (t (((R a) & (R b)) => ((a / b) = (a * (1 / b))))))",
   "(6 simplifyFocalPart (s 5))",
   "(7 rewrite (s 6) (path \"/right/right/right/right\") (t (((R a) & (R b)) => ((a * (1 / b)) = (a / b)))))",
   "(8 rewrite (s 7) (path \"/right/right/right\") (t (((((c != 0) & (R c)) & (R a)) & (R b)) => (((a / c) + (b / c)) = ((a + b) / c)))))",
   "(9 simplifyFocalPart (s 8))",
   "(10 divideBothByThis (s 9) (path \"/right/right/left/left\"))",
   "(11 simplifyProducts (s 10) (path \"/right/right\"))",
   "(12 reduceFraction (s 11) (path \"/right/right/right\"))"
  ]
 },
 {
  "doc": "/equations/#4",
  "proof": [
   "(1 consider (t (((5 * x) - (5 / 4)) = (2 / 3))))",
   "(2 addThisToBoth (s 1) (path \"/main/right/left/right\"))",
   "(3 simplifySums (s 2) (path \"/right/right\"))",
   "(4 commonDenominator (s 3) (path \"/right/right/right\"))",
   "(5 rewrite (s 4) (path \"/right/right/right\") (t (((((c != 0) & (R c)) & (R a)) & (R b)) => (((a / c) + (b / c)) = ((a + b) / c)))))",
   "(6 simplifyFocalPart (s 5))",
   "(7 divideBothByThis (s 6) (path \"/right/right/left/left\"))",
   "(8 simplifyProducts (s 7) (path \"/right/right\"))"
  ]
 },
 {
  "doc": "/equations/#5",
  "proof": [
   "(1 consider (t (((x - y) = 3) & ((y + 5) = x))))"
  ]
 },
 {
  "doc": "/equations/#6",
  "proof": [
   "(1 consider (t ((x = ((neg y) - 11)) & (((2 * x) - y) = 7))))"
  ]
 },
 {
  "doc": "/equations/#7",
  "proof": [
   "(1 consider (t ((12 / (x - 5)) = 4)))"
  ]
 },
 {
  "doc": "/equations/#8",
  "proof": [
   "(1 consider (t (((((6 * x) / (x - 4)) - (24 / (x - 4))) - 1) = 0)))"
  ]
 },
 {
  "doc": "/equations/#9",
  "proof": [
   "(1 consider (t ((((x + (14 / (x - 2))) - ((7 * x) / (x - 2))) - 1) = 0)))",
   "(2 consider (t ((x = 4) & (R x))))"
  ]
 },
 {
  "doc": "/equations2/",
  "proof": [
   "(1 consider (t (((x + y) = 5) & ((x - y) = 3))))",
   "(2 subtractThisFromBoth (s 1) (path \"/main/right/left/left/right\"))",
   "(3 simplifySite (s 2) (path \"/right/right/left/left\"))",
   "(4 replaceConjunct (s 3) (path \"/right/right/right/left/left\"))",
   "(5 rewrite (s 4) (path \"/right/right/right/left\") (t ((((R a) & (R b)) & (R c)) => (((a - b) - c) = (a - (b + c))))))",
   "(6 rewrite (s 5) (path \"/right/right/right/left/right\") (t ((R a) => ((a + a) = (2 * a)))))",
   "(7 addThisToBoth (s 6) (path \"/right/right/right/left/right\"))",
   "(8 simplifySums (s 7) (path \"/right/right/right\"))",
   "(9 rewrite (s 8) (path \"/right/right/right/left/left/left\") (t (((R a) & (R b)) => ((neg (a * b)) = ((neg a) * b)))))",
   "(10 simplifyFocalPart (s 9))",
   "(11 rewrite (s 10) (path \"/right/right/right/left/left\") (t ((((R a) & (R b)) & (R c)) => (((a * c) + (b * c)) = ((a + b) * c)))))",
   "(12 simplifyFocalPart (s 11))",
   "(13 subtractThisFromBoth (s 12) (path \"/right/right/right/right/right\"))",
   "(14 simplifySums (s 13) (path \"/right/right/right\"))",
   "(15 divideBothByThis (s 14) (path \"/right/right/right/right/left\"))",
   "(16 simplifyProducts (s 15) (path \"/right/right/right\"))",
   "(17 rewrite (s 16) (path \"/right/right/right\") (t ((x = y) == (y = x))))",
   "(18 replaceConjunct (s 17) (path \"/right/right/left/right/right\"))",
   "(19 simplifyFocalPart (s 18))"
  ]
 },
 {
  "doc": "/equations2/#2",
  "proof": [
   "(1 consider (t ((((5 * x) - 22) = y) & (((2 * y) + x) = 33))))",
   "(2 rewrite (s 1) (path \"/main/right/left\") (t ((x = y) == (y = x))))",
   "(3 replaceConjunct (s 2) (path \"/main/right/right/left/left/right\"))",
   "(4 rewrite (s 3) (path \"/main/right/right/left/left\") (t ((((R a) & (R b)) & (R c)) => ((a * (b - c)) = ((a * b) - (a * c))))))",
   "(5 simplifyProducts (s 4) (path \"/main/right/right/left/left\"))",
   "(6 addThisToBoth (s 5) (path \"/right/right/right/left/left/right\"))",
   "(7 simplifySums (s 6) (path \"/right/right/right\"))",
   "(8 rewrite (s 7) (path \"/right/right/right/left\") (t (((R a) & (R b)) => (((a * b) + b) = ((a + 1) * b)))))",
   "(9 simplifyProducts (s 8) (path \"/right/right/right/left\"))",
   "(10 divideBothByThis (s 9) (path \"/right/right/right/left/left\"))",
   "(11 simplifyProducts (s 10) (path \"/right/right/right\"))",
   "(12 replaceConjunct (s 11) (path \"/right/right/left/right/left/right\"))",
   "(13 simplifyFocalPart (s 12))"
  ]
 },
 {
  "doc": "/equations2/#3",
  "proof": [
   "(1 consider (t (((x - y) = 3) & ((y + 5) = x))))",
   "(2 rewrite (s 1) (path \"/main/right/right\") (t ((x = y) == (y = x))))",
   "(3 replaceConjunct (s 2) (path \"/main/right/left/left/left\"))",
   "(4 subtractThisFromBoth (s 3) (path \"/main/right/left/left/left/right\"))",
   "(5 simplifySums (s 4) (path \"/right/right/left\"))",
   "(6 simplifySite (s 5) (path \"/right/right/left\"))",
   "(7 simplifyFocalPart (s 6))"
  ]
 },
 {
  "doc": "/equations2/#4",
  "proof": [
   "(1 consider (t ((x = ((neg y) - 11)) & (((2 * x) - y) = 7))))"
  ]
 },
 {
  "doc": "/equations2/#5",
  "proof": [
   "(1 consider (t ((12 / (x - 5)) = 4)))"
  ]
 },
 {
  "doc": "/equations2/#6",
  "proof": [
   "(1 consider (t (((((6 * x) / (x - 4)) - (24 / (x - 4))) - 1) = 0)))"
  ]
 },
 {
  "doc": "/equations2/#7",
  "proof": [
   "(1 consider (t ((((x + (14 / (x - 2))) - ((7 * x) / (x - 2))) - 1) = 0)))"
  ]
 },
 {
  "doc": "/equations3/",
  "proof": [
   "(1 consider (t (((x - y) = 3) & ((y + 5) = x))))"
  ]
 },
 {
  "doc": "/equations3/#2",
  "proof": [
   "(1 consider (t ((x = ((neg y) - 11)) & (((2 * x) - y) = 7))))",
   "(2 replaceConjunct (s 1) (path \"/main/right/right/left/left/right\"))",
   "(3 rewrite (s 2) (path \"/main/right/right/left/left\") (t ((((R a) & (R b)) & (R c)) => ((a * (b - c)) = ((a * b) - (a * c))))))",
   "(4 simplifyProducts (s 3) (path \"/main/right/right/left/left\"))",
   "(5 addThisToBoth (s 4) (path \"/right/right/right/left/left/right\"))",
   "(6 simplifySums (s 5) (path \"/right/right/right\"))",
   "(7 rewrite (s 6) (path \"/right/right/right/left\") (t (((R a) & (R b)) => (((a * b) - b) = ((a - 1) * b)))))",
   "(8 simplifyProducts (s 7) (path \"/right/right/right/left\"))",
   "(9 divideBothByThis (s 8) (path \"/right/right/right/left/left\"))",
   "(10 simplifyProducts (s 9) (path \"/right/right/right\"))"
  ]
 },
 {
  "doc": "/equations3/#3",
  "proof": [
   "(1 consider (t ((12 / (x - 5)) = 4)))"
  ]
 },
 {
  "doc": "/equations3/#4",
  "proof": [
   "(1 consider (t (((((6 * x) / (x - 4)) - (24 / (x - 4))) - 1) = 0)))"
  ]
 },
 {
  "doc": "/equations3/#5",
  "proof": [
   "(1 consider (t ((((x + (14 / (x - 2))) - ((7 * x) / (x - 2))) - 1) = 0)))"
  ]
 },
 {
  "doc": "/equations4/",
  "proof": [
   "(1 consider (t ((x = ((neg y) - 11)) & (((2 * x) - y) = 7))))",
   "(2 replaceConjunct (s 1) (path \"/main/right/right/left/left/right\"))",
   "(3 rewrite (s 2) (path \"/main/right/right/left/left\") (t ((((R a) & (R b)) & (R c)) => ((a * (b - c)) = ((a * b) - (a * c))))))",
   "(4 simplifyProducts (s 3) (path \"/main/right/right/left/left\"))",
   "(5 addThisToBoth (s 4) (path \"/right/right/right/left/left/right\"))",
   "(6 simplifySums (s 5) (path \"/right/right/right\"))",
   "(7 rewrite (s 6) (path \"/right/right/right/left\") (t (((R a) & (R b)) => (((a * b) - b) = ((a - 1) * b)))))",
   "(8 simplifyProducts (s 7) (path \"/right/right/right/left\"))",
   "(9 divideBothByThis (s 8) (path \"/right/right/right/left/left\"))",
   "(10 simplifyProducts (s 9) (path \"/right/right/right\"))",
   "(11 replaceConjunct (s 10) (path \"/right/right/left/right/left/arg\"))",
   "(12 arrangeTerm (s 11) (path \"/right/right/left/right/left\"))",
   "(13 rewrite (s 12) (path \"/right/right/left/right\") (t ((((R b) & (R c)) & (c != 0)) => (((a / c) - b) = ((a / c) - ((b * c) / c))))))",
   "(14 rewrite (s 13) (path \"/right/right/left/right\") (t (((((c != 0) & (R c)) & (R a)) & (R b)) => (((a / c) - (b / c)) = ((a - b) / c)))))",
   "(15 simplifyFocalPart (s 14))"
  ]
 },
 {
  "doc": "/equations4/#2",
  "proof": [
   "(1 consider (t ((12 / (x - 5)) = 4)))"
  ]
 },
 {
  "doc": "/equations4/#3",
  "proof": [
   "(1 consider (t (((((6 * x) / (x - 4)) - (24 / (x - 4))) - 1) = 0)))"
  ]
 },
 {
  "doc": "/equations4/#4",
  "proof": [
   "(1 consider (t ((((x + (14 / (x - 2))) - ((7 * x) / (x - 2))) - 1) = 0)))"
  ]
 },
 {
  "doc": "/equations5/",
  "proof": [
   "(1 consider (t ((12 / (x - 5)) = 4)))",
   "(2 multiplyBothByThis (s 1) (path \"/main/right/left/right\"))",
   "(3 simplifyProducts (s 2) (path \"/right/right\"))",
   "(4 rewrite (s 3) (path \"/right/right/right\") (t ((((R a) & (R b)) & (R c)) => ((a * (b - c)) = ((a * b) - (a * c))))))",
   "(5 simplifyProducts (s 4) (path \"/right/right/right\"))",
   "(6 addThisToBoth (s 5) (path \"/right/right/right/right\"))",
   "(7 simplifySums (s 6) (path \"/right/right\"))",
   "(8 rewrite (s 7) (path \"/right/right\") (t ((x = y) == (y = x))))",
   "(9 divideBothByThis (s 8) (path \"/right/right/left/left\"))",
   "(10 simplifyProducts (s 9) (path \"/right/right\"))",
   "(11 copy (s 1))",
   "(12 andAssume (s 11) (t (x = 5)))",
   "(13 assumedEq (s 12) (path \"/right/right/left/right/left\") (t (x = 5)))",
   "(14 simplifyFocalPart (s 13))",
   "(15 copy (s 10))",
   "(16 rewrite (s 15) (path \"/left/left\") (t ((a != b) == (not (a = b)))))",
   "(17 addThisToBoth (s 16) (path \"/left/left/arg/left/right\"))",
   "(18 simplifySums (s 17) (path \"/left/left/arg\"))",
   "(19 extractHyp (s 18) (t (R x)))",
   "(20 andAssume (s 14) (t (R x)))",
   "(21 extractHyp (s 20) (t (R x)))",
   "(22 rewrite (s 21) (path \"/right\") (t ((a => (b == c)) == ((a & b) == (a & c)))))",
   "(23 simplifyFocalPart (s 22))",
   "(24 rewrite (s 19) (path \"/right\") (t ((a => (b == c)) == ((a & b) == (a & c)))))",
   "(25 chain0 (s 23) (t ((a => (b == c)) => ((z => (b == d)) => (((a | z) & b) == ((a & c) | (z & d)))))))",
   "(26 chain0 (s 24) (s 25))",
   "(27 simplifyFocalPart (s 26))",
   "(28 considerPart (s 27) (path \"/main/left/left\"))",
   "(29 simplifyFocalPart (s 28))",
   "(30 rewriteFrom (s 27) (path \"/main/left/left\") (s 29))"
  ]
 },
 {
  "doc": "/equations5/#2",
  "proof": [
   "(1 consider (t (((((3 * x) / (x - 4)) - (12 / (x - 4))) - 1) = 0)))"
  ]
 },
 {
  "doc": "/equations5/#3",
  "proof": [
   "(1 consider (t ((((x + (14 / (x - 2))) - ((7 * x) / (x - 2))) - 1) = 0)))"
  ]
 }
];
