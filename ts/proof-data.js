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
   "(8 rewrite (s 7) (path \"/right/right\") (t ((x = y) == (y = x))))",
   "(9 divideBothByThis (s 8) (path \"/right/right/left/left\"))",
   "(10 simplifyProducts (s 9) (path \"/right/right\"))"
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
		"(11 considerPart (s 10) (path \"/right\"))",
		"(12 andAssume (s 11) (t ((x = 5) & (R x))))",
		"(13 assumedEq (s 12) (path \"/right/right/left/left/right/left\") (t (x = 5)))",
		"(14 simplifyFocalPart (s 13))",
		"(15 assumedEq (s 14) (path \"/right/right/right/left\") (t (x = 5)))",
		"(16 simplifySite (s 15) \"\")",
		"(17 copy (s 10))",
		"(18 rewrite (s 17) (path \"/left/left\") (t ((x != y) == (not (x = y)))))",
		"(19 addThisToBoth (s 18) (path \"/left/left/arg/left/right\"))",
		"(20 simplifySums (s 19) (path \"/left/left/arg\"))",
		"(21 isolateAsm (s 20) (t (not (x = 5))))",
		"(22 isolateAsm (s 16) (t (x = 5)))",
		"(23 chain0 (s 22) (t ((a => b) => (((not a) => b) => b))))",
		"(24 trueBy0 (s 23) (path \"/left\") (s 21))",
		"(25 simplifySite (s 24) \"\")"
	 ]
 },
 {
  "doc": "/equations5/#2",
  "proof": [
   "(1 consider (t (((((3 * x) / (x - 4)) - (12 / (x - 4))) - 1) = 0)))",
   "(2 multiplyBothByThis (s 1) (path \"/main/right/left/left/left/right\"))",
   "(3 simplifyProducts (s 2) (path \"/right/right\"))",
   "(4 rewrite (s 3) (path \"/right/right/left\") (t (((R a) & (R b)) => (((a - 1) * b) = ((a * b) - b)))))",
   "(5 rewrite (s 4) (path \"/right/right/left/left\") (t ((((R a) & (R b)) & (R c)) => (((a - b) * c) = ((a * c) - (b * c))))))",
   "(6 simplifyProducts (s 5) (path \"/right/right/left/left\"))",
   "(7 rewrite (s 6) (path \"/right/right/left\") (t ((((R a) & (R b)) & (R c)) => ((a - (b - c)) = ((a - b) + c)))))",
   "(8 addThisToBoth (s 7) (path \"/right/right/left/left/left/right\"))",
   "(9 simplifySums (s 8) (path \"/right/right\"))",
   "(10 subtractThisFromBoth (s 9) (path \"/right/right/left/right\"))",
   "(11 simplifySums (s 10) (path \"/right/right\"))",
   "(12 rewrite (s 11) (path \"/right/right/left\") (t (((R a) & (R b)) => (((a * b) - b) = ((a - 1) * b)))))",
   "(13 simplifyProducts (s 12) (path \"/right/right/left\"))",
   "(14 divideBothByThis (s 13) (path \"/right/right/left/left\"))",
   "(15 simplifyProducts (s 14) (path \"/right/right\"))",
   "(16 copy (s 15))",
   "(17 rewrite (s 16) (path \"/left/left\") (t ((a != b) == (not (a = b)))))",
   "(18 addThisToBoth (s 17) (path \"/left/left/arg/left/right\"))",
   "(19 simplifySums (s 18) (path \"/left/left/arg\"))",
   "(20 rewrite (s 19) (path \"/right\") (t ((a == b) == ((not a) == (not b)))))",
   "(21 assumed (s 20) (path \"/right/right\"))",
   "(22 simplifySite (s 21) (path \"/right\"))",
   "(23 considerPart (s 19) (path \"/right\"))",
   "(24 andAssume (s 23) (t (x = 4)))",
   "(25 assumedEq (s 24) (path \"/right/right/left/left/left/left/right/left\") (t (x = 4)))",
   "(26 simplifyFocalPart (s 25))",
   "(27 assumedEq (s 26) (path \"/right/right/right/left\") (t (x = 4)))",
   "(28 simplifyFocalPart (s 27))",
   "(29 rewrite (s 28) (path \"/right\") (t ((a == F) == (not a))))",
   "(30 copy (s 29))",
   "(31 extractHyp (s 30) (t (R x)))",
   "(32 copy (s 22))",
   "(33 extractHyp (s 32) (t (R x)))",
   "(34 chain0 (s 31) (t ((a => b) => (((not a) => b) => b))))",
   "(35 rewrite (s 33) (path \"\") (t (a == (a == T))))",
   "(36 assumed (s 31) (path \"/right/right/arg/right\"))",
   "(37 chain0 (s 36) (t ((a => b) => (((not a) => b) => b))))",
   "(38 simplifySite (s 37) (path \"/left\"))",
   "(39 simplifyFocalPart (s 38))",
   "(40 rewriteFrom (s 38) (path \"/left\") (s 35))",
   "(41 simplifyFocalPart (s 40))",
   "(42 rewrite (s 41) (path \"/right\") (t ((not (x = y)) == (x != y))))",
   "(43 copy (s 42))"
  ]
 },
 {
  "doc": "/equations5/#3",
  "proof": [
   "(1 consider (t ((((x + (14 / (x - 2))) - ((7 * x) / (x - 2))) - 1) = 0)))"
  ]
 },
 {
  "doc": "/fake-proof/",
  "proof": [
   "(1 assumeExplicitly (t (x = y)))",
   "(2 consider (t (x * x)))",
   "(3 rewriteFrom (s 2) (path \"/main/right/right\") (s 1))",
   "(4 subtractFromBoth (s 3) (path \"/right\") (t (y * y)))",
   "(5 rewrite (s 4) (path \"/right/left\") (t (((R x) & (R y)) => (((x * x) - (y * y)) = ((x + y) * (x - y))))))",
   "(6 rewrite (s 5) (path \"/right/right\") (t ((((R a) & (R b)) & (R c)) => (((a * c) - (b * c)) = ((a - b) * c)))))",
   "(7 rewrite (s 6) (path \"/right/right\") (t (((R x) & (R y)) => ((x * y) = (y * x)))))",
   "(8 divideBothByThis (s 7) (path \"/right/right/right\"))",
   "(9 rewrite (s 8) (path \"/right/left\") (t ((((b != 0) & (R b)) & (R a)) => (((a * b) / b) = a))))",
   "(10 simplifyFocalPart (s 9))",
   "(11 assumedEq (s 10) (path \"/right/left/left\") (t (x = y)))",
   "(12 rewrite (s 11) (path \"/right/left\") (t ((R a) => ((a + a) = (2 * a)))))",
   "(13 divideBothByThis (s 12) (path \"/right/right\"))",
   "(14 simplifyProducts (s 13) (path \"/right\"))",
   "(15 display (s 14))",
   "(16 rewrite (s 15) (path \"/left/left/right\") (t ((a != b) == (not (a = b)))))",
   "(17 rewrite (s 16) (path \"/left/left/right/arg\") (t (((R a) & (R b)) => (((a - b) = 0) == (a = b)))))",
   "(18 assumed (s 17) (path \"/left/left/right/arg\"))",
   "(19 simplifySite (s 18) (path \"/left\"))"
  ]
 },
 {
  "doc": "/lunar/",
  "proof": [
   "(1 assumeExplicitly (t (A == (((4 * pi) * (r ** 2)) = (((4 / 3) * pi) * (r ** 3))))))",
   "(2 subtractThisFromBoth (s 1) (path \"/right/right/right\"))",
   "(3 simplifySums (s 2) (path \"/right/right\"))",
   "(4 rewrite (s 3) (path \"/right/right/left/right/right\") (t ((R x) => ((x ** 3) = ((x ** 2) * x)))))",
   "(5 rewrite (s 4) (path \"/right/right/left/right/right\") (t (((R x) & (R y)) => ((x * y) = (y * x)))))",
   "(6 flattenTerm (s 5) (path \"/right/right/left/right\"))",
   "(7 rewrite (s 6) (path \"/right/right/left\") (t ((((R a) & (R b)) & (R c)) => (((a * c) - (b * c)) = ((a - b) * c)))))",
   "(8 rewrite (s 7) (path \"/right/right\") (t (((R x) & (R y)) => (((x * y) = 0) == ((x = 0) | (y = 0))))))",
   "(9 simplifyFocalPart (s 8))",
   "(10 multiplyBoth (s 9) (path \"/right/right/left\") (t 3))",
   "(11 simplifyProducts (s 10) (path \"/right/right/left\"))",
   "(12 rewrite (s 11) (path \"/right/right/left/left\") (t ((((R a) & (R b)) & (R c)) => ((a * (b - c)) = ((a * b) - (a * c))))))",
   "(13 simplifyProducts (s 12) (path \"/right/right/left/left\"))",
   "(14 rewrite (s 13) (path \"/right/right/left/left/right\") (t ((((((b != 0) & (c != 0)) & (R b)) & (R c)) & (R a)) => (((a * c) / b) = (a / (b / c))))))",
   "(15 rewrite (s 14) (path \"/right/right/left/left/right\") (t (((((c != 0) & (R c)) & (R a)) & (R b)) => (((a * b) / c) = ((a / c) * b)))))",
   "(16 rewrite (s 15) (path \"/right/right/left/left/right/left\") (t ((((((b != 0) & (c != 0)) & (R b)) & (R c)) & (R a)) => ((a / (b / c)) = ((a / b) * c)))))",
   "(17 simplifyFocalPart (s 16))"
  ]
 }];
