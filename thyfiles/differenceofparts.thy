theory differenceofparts
	imports Axioms Definitions Theorems
begin

theorem differenceofparts:
	assumes: `axioms`
		"seg_eq A B a b"
		"seg_eq A C a c"
		"bet A B C"
		"bet a b c"
	shows: "seg_eq B C b c"
proof -
	consider "B = A"|"B \<noteq> A" by blast
	hence seg_eq B C b c
	proof (cases)
		case 1
		have "seg_eq A A a b" using `seg_eq A B a b` `B = A` by blast
		have "seg_eq a b A A" using congruencesymmetric[OF `axioms` `seg_eq A A a b`] .
		have "a = b" using nullsegment1E[OF `axioms` `seg_eq a b A A`] .
		have "seg_eq A C A C" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq B C A C" using `seg_eq A C A C` `B = A` by blast
		have "seg_eq B C a c" using congruencetransitive[OF `axioms` `seg_eq B C A C` `seg_eq A C a c`] .
		have "seg_eq b c b c" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq b c a c" using `seg_eq b c b c` `a = b` by blast
		have "seg_eq a c b c" using congruencesymmetric[OF `axioms` `seg_eq b c a c`] .
		have "seg_eq B C b c" using congruencetransitive[OF `axioms` `seg_eq B C a c` `seg_eq a c b c`] .
	next
		case 2
		have "\<not> (C = A)"
		proof (rule ccontr)
			assume "C = A"
			have "bet A B A" using `bet A B C` `C = A` by blast
			have "\<not> (bet A B A)" using betweennessidentityE[OF `axioms`] by blast
			show "False" using `\<not> (bet A B A)` `bet A B A` by blast
		qed
		hence "C \<noteq> A" by blast
		have "A \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> A`] .
		obtain E where "bet C A E \<and> seg_eq A E A C" using extensionE[OF `axioms` `C \<noteq> A` `A \<noteq> C`] by blast
		have "seg_eq A C a c" using `seg_eq A C a c` .
		have "bet C A E" using `bet C A E \<and> seg_eq A E A C` by blast
		have "A \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> A`] .
		have "a \<noteq> c" using nullsegment3[OF `axioms` `A \<noteq> C` `seg_eq A C a c`] .
		have "\<not> (c = a)"
		proof (rule ccontr)
			assume "c = a"
			have "a = c" using equalitysymmetric[OF `axioms` `c = a`] .
			show "False" using `a = c` `a \<noteq> c` by blast
		qed
		hence "c \<noteq> a" by blast
		have "a \<noteq> c" using inequalitysymmetric[OF `axioms` `c \<noteq> a`] .
		have "bet c a e \<and> seg_eq a e a c" using extensionE[OF `axioms` `c \<noteq> a` `a \<noteq> c`] by blast
		have "bet c a e" using `bet c a e \<and> seg_eq a e a c` by blast
		have "seg_eq A E A C" using `bet C A E \<and> seg_eq A E A C` by blast
		have "seg_eq a e a c" using `bet c a e \<and> seg_eq a e a c` by blast
		have "seg_eq E A A E" using equalityreverseE[OF `axioms`] by blast
		have "seg_eq E A A C" using congruencetransitive[OF `axioms` `seg_eq E A A E` `seg_eq A E A C`] .
		have "seg_eq A C a c" using `seg_eq A C a c` .
		have "seg_eq E A a c" using congruencetransitive[OF `axioms` `seg_eq E A A C` `seg_eq A C a c`] .
		have "seg_eq e a a e" using equalityreverseE[OF `axioms`] by blast
		have "seg_eq e a a c" using congruencetransitive[OF `axioms` `seg_eq e a a e` `seg_eq a e a c`] .
		have "seg_eq a c e a" using congruencesymmetric[OF `axioms` `seg_eq e a a c`] .
		have "seg_eq E A a c" using congruencetransitive[OF `axioms` `seg_eq E A A C` `seg_eq A C a c`] .
		have "seg_eq E A e a" using congruencetransitive[OF `axioms` `seg_eq E A a c` `seg_eq a c e a`] .
		have "bet E A C" using betweennesssymmetryE[OF `axioms` `bet C A E`] .
		have "bet e a c" using betweennesssymmetryE[OF `axioms` `bet c a e`] .
		have "seg_eq E C e c" using sumofparts[OF `axioms` `seg_eq E A e a` `seg_eq A C a c` `bet E A C` `bet e a c`] .
		have "seg_eq E C e c" using `seg_eq E C e c` .
		have "seg_eq E A e a" using `seg_eq E A e a` .
		have "seg_eq A B a b" using `seg_eq A B a b` .
		have "bet E A C" using `bet E A C` .
		have "bet A B C" using `bet A B C` .
		have "bet E A B" using innertransitivityE[OF `axioms` `bet E A C` `bet A B C`] .
		have "bet e a b" using innertransitivityE[OF `axioms` `bet e a c` `bet a b c`] .
		have "seg_eq C B c b" using 5-lineE[OF `axioms` `seg_eq A B a b` `seg_eq E C e c` `seg_eq A C a c` `bet E A B` `bet e a b` `seg_eq E A e a`] .
		have "seg_eq b c B C" using doublereverse[OF `axioms` `seg_eq C B c b`] by blast
		have "seg_eq B C b c" using congruencesymmetric[OF `axioms` `seg_eq b c B C`] .
	next
	thus ?thesis by blast
qed

end