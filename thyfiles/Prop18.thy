theory Prop18
	imports Axioms Definitions Theorems
begin

theorem Prop18:
	assumes: `axioms`
		"triangle A B C"
		"seg_lt A B A C"
	shows: "ang_lt B C A A B C"
proof -
	have "\<not> col A B C" sorry
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "col A B C" using col_b `axioms` `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "col A B C" using col_b `axioms` `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> C`] .
	have "seg_eq A C A C" using congruencereflexiveE[OF `axioms`] .
	obtain D where "bet A D C \<and> seg_eq A D A B" using Prop03[OF `axioms` `seg_lt A B A C` `seg_eq A C A C`]  by  blast
	have "bet A D C" using `bet A D C \<and> seg_eq A D A B` by blast
	have "\<not> (col B C D)"
	proof (rule ccontr)
		assume "col B C D"
		have "col D C B" using collinearorder[OF `axioms` `col B C D`] by blast
		have "col A D C" using col_b `axioms` `bet A D C \<and> seg_eq A D A B` by blast
		have "col D C A" using collinearorder[OF `axioms` `col A D C`] by blast
		have "D \<noteq> C" using betweennotequal[OF `axioms` `bet A D C`] by blast
		have "col C B A" using collinear4[OF `axioms` `col D C B` `col D C A` `D \<noteq> C`] .
		have "col A B C" using collinearorder[OF `axioms` `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B C D" by blast
	have "triangle B C D" sorry
	have "bet C D A" using betweennesssymmetryE[OF `axioms` `bet A D C`] .
	have "ang_lt D C B B D A" using Prop16[OF `axioms` `triangle B C D` `bet C D A`] by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col B C D" using col_b `axioms` `B = C` by blast
		show "False" using `col B C D` `\<not> col B C D` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	have "\<not> (col A D B)"
	proof (rule ccontr)
		assume "col A D B"
		have "col A D C" using col_b `axioms` `bet A D C \<and> seg_eq A D A B` by blast
		have "col D A C" using collinearorder[OF `axioms` `col A D C`] by blast
		have "col D A B" using collinearorder[OF `axioms` `col A D B`] by blast
		have "A \<noteq> D" using betweennotequal[OF `axioms` `bet A D C`] by blast
		have "D \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> D`] .
		have "col A C B" using collinear4[OF `axioms` `col D A C` `col D A B` `D \<noteq> A`] .
		have "col A B C" using collinearorder[OF `axioms` `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A D B" by blast
	have "triangle A D B" sorry
	have "seg_eq A D A B" using `bet A D C \<and> seg_eq A D A B` by blast
	have "tri_isos A D B" sorry
	have "ang_eq A D B A B D" using Prop05[OF `axioms` `tri_isos A D B`] .
	have "ray_on C A D" using ray4 `axioms` `bet C D A` `C \<noteq> A` by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "ray_on C B B" using ray4 `axioms` `B = B` `C \<noteq> B` by blast
	have "\<not> (col A C B)"
	proof (rule ccontr)
		assume "col A C B"
		have "col A B C" using collinearorder[OF `axioms` `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A C B" by blast
	have "ang_eq A C B A C B" using equalanglesreflexive[OF `axioms` `\<not> col A C B`] .
	have "ang_eq A C B D C B" using equalangleshelper[OF `axioms` `ang_eq A C B A C B` `ray_on C A D` `ray_on C B B`] .
	have "ang_lt A C B B D A" using angleorderrespectscongruence2[OF `axioms` `ang_lt D C B B D A` `ang_eq A C B D C B`] .
	have "ang_eq A D B B D A" using ABCequalsCBA[OF `axioms` `\<not> col A D B`] .
	have "ang_lt A C B A D B" using angleorderrespectscongruence[OF `axioms` `ang_lt A C B B D A` `ang_eq A D B B D A`] .
	have "ang_eq A D B A B D" using `ang_eq A D B A B D` .
	have "ang_eq A B D A D B" using equalanglessymmetric[OF `axioms` `ang_eq A D B A B D`] .
	have "ang_lt A C B A B D" using angleorderrespectscongruence[OF `axioms` `ang_lt A C B A D B` `ang_eq A B D A D B`] .
	have "\<not> (col B C A)"
	proof (rule ccontr)
		assume "col B C A"
		have "col A B C" using collinearorder[OF `axioms` `col B C A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B C A" by blast
	have "ang_eq B C A A C B" using ABCequalsCBA[OF `axioms` `\<not> col B C A`] .
	have "ang_lt B C A A B D" using angleorderrespectscongruence2[OF `axioms` `ang_lt A C B A B D` `ang_eq B C A A C B`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "ray_on B C C" using ray4 `axioms` `C = C` `B \<noteq> C` by blast
	have "ray_on B A A" using ray4 `axioms` `A = A` `B \<noteq> A` by blast
	have "bet A D C" using `bet A D C` .
	have "\<not> (col A B D)"
	proof (rule ccontr)
		assume "col A B D"
		have "col A D B" using collinearorder[OF `axioms` `col A B D`] by blast
		show "False" using `col A D B` `\<not> col A D B` by blast
	qed
	hence "\<not> col A B D" by blast
	have "ang_eq A B D A B D" using equalanglesreflexive[OF `axioms` `\<not> col A B D`] .
	have "ang_lt A B D A B C" sorry
	have "ang_lt B C A A B C" using angleordertransitive[OF `axioms` `ang_lt B C A A B D` `ang_lt A B D A B C`] .
	thus ?thesis by blast
qed

end