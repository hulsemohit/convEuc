theory interior5
	imports Axioms Definitions Theorems
begin

theorem interior5:
	assumes: `axioms`
		"bet A B C"
		"bet a b c"
		"seg_eq A B a b"
		"seg_eq B C b c"
		"seg_eq A D a d"
		"seg_eq C D c d"
	shows: "seg_eq B D b d"
proof -
	have "B \<noteq> C" using betweennotequal[OF `axioms` `bet A B C`] by blast
	have "A \<noteq> C" using betweennotequal[OF `axioms` `bet A B C`] by blast
	have "\<not> (C = A)"
	proof (rule ccontr)
		assume "C = A"
		have "A = C" using equalitysymmetric[OF `axioms` `C = A`] .
		show "False" using `A = C` `A \<noteq> C` by blast
	qed
	hence "C \<noteq> A" by blast
	obtain M where "bet C A M \<and> seg_eq A M B C" using extensionE[OF `axioms` `C \<noteq> A` `B \<noteq> C`]  by  blast
	have "seg_eq A M B C" using `bet C A M \<and> seg_eq A M B C` by blast
	have "seg_eq A M M A" using equalityreverseE[OF `axioms`] .
	have "seg_eq M A A M" using congruencesymmetric[OF `axioms` `seg_eq A M M A`] .
	have "seg_eq M A B C" using congruencetransitive[OF `axioms` `seg_eq M A A M` `seg_eq A M B C`] .
	have "seg_eq B C b c" using `seg_eq B C b c` .
	have "B \<noteq> C" using `B \<noteq> C` .
	have "b \<noteq> c" using nullsegment3[OF `axioms` `B \<noteq> C` `seg_eq B C b c`] .
	have "a \<noteq> c" using betweennotequal[OF `axioms` `bet a b c`] by blast
	have "\<not> (c = a)"
	proof (rule ccontr)
		assume "c = a"
		have "a = c" using equalitysymmetric[OF `axioms` `c = a`] .
		show "False" using `a = c` `a \<noteq> c` by blast
	qed
	hence "c \<noteq> a" by blast
	obtain m where "bet c a m \<and> seg_eq a m b c" using extensionE[OF `axioms` `c \<noteq> a` `b \<noteq> c`]  by  blast
	have "bet c a m" using `bet c a m \<and> seg_eq a m b c` by blast
	have "seg_eq a m b c" using `bet c a m \<and> seg_eq a m b c` by blast
	have "seg_eq m a a m" using equalityreverseE[OF `axioms`] .
	have "seg_eq m a b c" using congruencetransitive[OF `axioms` `seg_eq m a a m` `seg_eq a m b c`] .
	have "seg_eq M A B C" using `seg_eq M A B C` .
	have "seg_eq B C b c" using `seg_eq B C b c` .
	have "seg_eq b c m a" using congruencesymmetric[OF `axioms` `seg_eq m a b c`] .
	have "seg_eq B C m a" using congruencetransitive[OF `axioms` `seg_eq B C b c` `seg_eq b c m a`] .
	have "seg_eq M A m a" using congruencetransitive[OF `axioms` `seg_eq M A B C` `seg_eq B C m a`] .
	have "seg_eq A B a b" using `seg_eq A B a b` .
	have "seg_eq B C b c" using `seg_eq B C b c` .
	have "seg_eq A C a c" using sumofparts[OF `axioms` `seg_eq A B a b` `seg_eq B C b c` `bet A B C` `bet a b c`] .
	have "seg_eq c a C A" using doublereverse[OF `axioms` `seg_eq A C a c`] by blast
	have "seg_eq C A c a" using congruencesymmetric[OF `axioms` `seg_eq c a C A`] .
	have "bet C A M" using `bet C A M \<and> seg_eq A M B C` by blast
	have "bet C B A" using betweennesssymmetryE[OF `axioms` `bet A B C`] .
	have "bet B A M" using n3_6a[OF `axioms` `bet C B A` `bet C A M`] .
	have "bet c b a" using betweennesssymmetryE[OF `axioms` `bet a b c`] .
	have "bet b a m" using n3_6a[OF `axioms` `bet c b a` `bet c a m`] .
	have "seg_eq A M a m" using congruenceflip[OF `axioms` `seg_eq M A m a`] by blast
	have "seg_eq A D a d" using `seg_eq A D a d` .
	have "seg_eq D M d m" using 5-lineE[OF `axioms` `seg_eq A M a m` `seg_eq C D c d` `seg_eq A D a d` `bet C A M` `bet c a m` `seg_eq C A c a`] .
	have "seg_eq M A m a" using `seg_eq M A m a` .
	have "bet m a b" using betweennesssymmetryE[OF `axioms` `bet b a m`] .
	have "bet M A B" using betweennesssymmetryE[OF `axioms` `bet B A M`] .
	have "seg_eq A D a d" using `seg_eq A D a d` .
	have "seg_eq M D m d" using congruenceflip[OF `axioms` `seg_eq D M d m`] by blast
	have "seg_eq A B a b" using `seg_eq A B a b` .
	have "seg_eq D B d b" using 5-lineE[OF `axioms` `seg_eq A B a b` `seg_eq M D m d` `seg_eq A D a d` `bet M A B` `bet m a b` `seg_eq M A m a`] .
	have "seg_eq B D b d" using congruenceflip[OF `axioms` `seg_eq D B d b`] by blast
	thus ?thesis by blast
qed

end