theory Prop13
	imports Axioms Definitions Theorems
begin

theorem Prop13:
	assumes: `axioms`
		"bet D B C"
		"\<not> col A B C"
	shows: "ang_suppl C B A A B D"
proof -
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "B \<noteq> A" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	have "ray_on B A A" using ray4 `axioms` `A = A` `B \<noteq> A` by blast
	have "bet C B D" using betweennesssymmetryE[OF `axioms` `bet D B C`] .
	have "linear_pair C B A A D" using supplement_b[OF `axioms` `ray_on B A A` `bet C B D`] .
	have "\<not> col C B A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "col D B C" using collinear_b `axioms` `bet D B C` by blast
	have "col C B D" using collinearorder[OF `axioms` `col D B C`] by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col C B B" using collinear_b `axioms` `B = B` by blast
	have "D \<noteq> B" using betweennotequal[OF `axioms` `bet D B C`] by blast
	have "\<not> col D B A" using NChelper[OF `axioms` `\<not> col C B A` `col C B D` `col C B B` `D \<noteq> B`] .
	have "\<not> col A B D" using NCorder[OF `axioms` `\<not> col D B A`] by blast
	have "ang_eq A B D A B D" using equalanglesreflexive[OF `axioms` `\<not> col A B D`] .
	have "ang_eq C B A C B A" using equalanglesreflexive[OF `axioms` `\<not> col C B A`] .
	have "ang_suppl C B A A B D" using tworightangles_b[OF `axioms` `linear_pair C B A A D` `ang_eq C B A C B A` `ang_eq A B D A B D`] .
	thus ?thesis by blast
qed

end