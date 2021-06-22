theory legsmallerhypotenuse
	imports Axioms Definitions Theorems
begin

theorem legsmallerhypotenuse:
	assumes: `axioms`
		"ang_right A B C"
	shows: "seg_lt A B A C \<and> seg_lt B C A C"
proof -
	have "ang_right C B A" using n8_2[OF `axioms` `ang_right A B C`] .
	obtain D where "bet C B D \<and> seg_eq C B D B \<and> seg_eq C A D A \<and> B \<noteq> A" using rightangle_f[OF `axioms` `ang_right C B A`] by blast
	have "bet C B D" using `bet C B D \<and> seg_eq C B D B \<and> seg_eq C A D A \<and> B \<noteq> A` by blast
	have "seg_eq C B D B" using `bet C B D \<and> seg_eq C B D B \<and> seg_eq C A D A \<and> B \<noteq> A` by blast
	have "seg_eq C A D A" using `bet C B D \<and> seg_eq C B D B \<and> seg_eq C A D A \<and> B \<noteq> A` by blast
	have "B \<noteq> A" using `bet C B D \<and> seg_eq C B D B \<and> seg_eq C A D A \<and> B \<noteq> A` by blast
	have "\<not> col A B C" using rightangleNC[OF `axioms` `ang_right A B C`] .
	have "triangle A B C" using triangle_b[OF `axioms` `\<not> col A B C`] .
	have "\<not> (col A C B)"
	proof (rule ccontr)
		assume "col A C B"
		have "col A B C" using collinearorder[OF `axioms` `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A C B" by blast
	have "triangle A C B" using triangle_b[OF `axioms` `\<not> col A C B`] .
	have "ang_lt C A B A B D \<and> ang_lt B C A A B D" using Prop16[OF `axioms` `triangle A C B` `bet C B D`] .
	have "ang_lt C A B A B D" using `ang_lt C A B A B D \<and> ang_lt B C A A B D` by blast
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" using collinear_b `axioms` `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "B \<noteq> D" using betweennotequal[OF `axioms` `bet C B D`] by blast
	have "ray_on B A A" using ray4 `axioms` `A = A` `bet C B D \<and> seg_eq C B D B \<and> seg_eq C A D A \<and> B \<noteq> A` by blast
	have "ray_on B C C" using ray4 `axioms` `C = C` `B \<noteq> C` by blast
	have "ray_on B D D" using ray4 `axioms` `D = D` `B \<noteq> D` by blast
	have "seg_eq B A B A" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq B D B C" using doublereverse[OF `axioms` `seg_eq C B D B`] by blast
	have "seg_eq A D A C" using doublereverse[OF `axioms` `seg_eq C A D A`] by blast
	have "\<not> (col A B D)"
	proof (rule ccontr)
		assume "col A B D"
		have "col C B D" using collinear_b `axioms` `bet C B D \<and> seg_eq C B D B \<and> seg_eq C A D A \<and> B \<noteq> A` by blast
		have "col D B C" using collinearorder[OF `axioms` `col C B D`] by blast
		have "col D B A" using collinearorder[OF `axioms` `col A B D`] by blast
		have "B \<noteq> D" using betweennotequal[OF `axioms` `bet C B D`] by blast
		have "D \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> D`] .
		have "col B C A" using collinear4[OF `axioms` `col D B C` `col D B A` `D \<noteq> B`] .
		have "col A B C" using collinearorder[OF `axioms` `col B C A`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col A B D" by blast
	have "ang_eq A B D A B C" using equalangles_b[OF `axioms` `ray_on B A A` `ray_on B D D` `ray_on B A A` `ray_on B C C` `seg_eq B A B A` `seg_eq B D B C` `seg_eq A D A C` `\<not> col A B D`] .
	have "ang_eq A B C A B D" using equalanglessymmetric[OF `axioms` `ang_eq A B D A B C`] .
	have "ang_lt B C A A B D" using `ang_lt C A B A B D \<and> ang_lt B C A A B D` by blast
	have "ang_lt B C A A B C" using angleorderrespectscongruence[OF `axioms` `ang_lt B C A A B D` `ang_eq A B C A B D`] .
	have "triangle A B C" using `triangle A B C` .
	have "seg_lt A B A C" using Prop19[OF `axioms` `triangle A B C` `ang_lt B C A A B C`] .
	have "ang_lt C A B A B C" using angleorderrespectscongruence[OF `axioms` `ang_lt C A B A B D` `ang_eq A B C A B D`] .
	have "\<not> (col B A C)"
	proof (rule ccontr)
		assume "col B A C"
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col B A C" by blast
	have "ang_eq B A C C A B" using ABCequalsCBA[OF `axioms` `\<not> col B A C`] .
	have "ang_lt B A C A B C" using angleorderrespectscongruence2[OF `axioms` `ang_lt C A B A B C` `ang_eq B A C C A B`] .
	have "\<not> (col C B A)"
	proof (rule ccontr)
		assume "col C B A"
		have "col A B C" using collinearorder[OF `axioms` `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col C B A" by blast
	have "triangle C B A" using triangle_b[OF `axioms` `\<not> col C B A`] .
	have "ang_eq C B A A B C" using ABCequalsCBA[OF `axioms` `\<not> col C B A`] .
	have "ang_lt B A C C B A" using angleorderrespectscongruence[OF `axioms` `ang_lt B A C A B C` `ang_eq C B A A B C`] .
	have "seg_lt C B C A" using Prop19[OF `axioms` `triangle C B A` `ang_lt B A C C B A`] .
	have "seg_eq C B B C" using equalityreverseE[OF `axioms`] by blast
	have "seg_lt B C C A" using lessthancongruence2[OF `axioms` `seg_lt C B C A` `seg_eq C B B C`] .
	have "seg_eq C A A C" using equalityreverseE[OF `axioms`] by blast
	have "seg_lt B C A C" using lessthancongruence[OF `axioms` `seg_lt B C C A` `seg_eq C A A C`] .
	have "seg_lt A B A C \<and> seg_lt B C A C" using `seg_lt A B A C` `seg_lt B C A C` by blast
	thus ?thesis by blast
qed

end