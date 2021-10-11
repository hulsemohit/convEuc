theory Prop34
	imports ABCequalsCBA Geometry NCorder Prop26A Prop29B angledistinct collinearorder congruenceflip congruencesymmetric diagonalsmeet equalanglesNC equalanglesflip equalanglestransitive inequalitysymmetric parallelflip ray4
begin

theorem(in euclidean_geometry) Prop34:
	assumes 
		"parallelogram A C D B"
	shows "seg_eq A B C D \<and> seg_eq A C B D \<and> ang_eq C A B B D C \<and> ang_eq A B D D C A \<and> tri_cong C A B B D C"
proof -
	have "parallel A C D B \<and> parallel A B C D" using parallelogram_f[OF `parallelogram A C D B`] .
	have "parallel A C D B" using `parallel A C D B \<and> parallel A B C D` by blast
	have "parallel A B C D" using `parallel A C D B \<and> parallel A B C D` by blast
	have "parallel A C B D" using parallelflip[OF `parallel A C D B`] by blast
	obtain M where "bet A M D \<and> bet C M B" using diagonalsmeet[OF `parallelogram A C D B`]  by  blast
	have "bet A M D" using `bet A M D \<and> bet C M B` by blast
	have "bet C M B" using `bet A M D \<and> bet C M B` by blast
	have "bet B M C" using betweennesssymmetryE[OF `bet C M B`] .
	have "col B M C" using collinear_b `bet B M C` by blast
	have "col B C M" using collinearorder[OF `col B M C`] by blast
	have "\<not> (meets A B C D)" using parallel_f[OF `parallel A B C D`] by fastforce
	have "A \<noteq> B" using parallel_f[OF `parallel A B C D`] by fastforce
	have "C \<noteq> D" using parallel_f[OF `parallel A B C D`] by fastforce
	have "\<not> (col B C A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B C A))"
hence "col B C A" by blast
		have "col A B C" using collinearorder[OF `col B C A`] by blast
		have "C = C" using equalityreflexiveE.
		have "col C D C" using collinear_b `C = C` by blast
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B C \<and> col C D C" using `A \<noteq> B` `C \<noteq> D` `col A B C` `col C D C` by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B C` `col C D C`] .
		show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
	qed
	hence "\<not> col B C A" by blast
	have "bet A M D \<and> col B C M \<and> \<not> col B C A" using `bet A M D \<and> bet C M B` `col B C M` `\<not> col B C A` by blast
	have "oppo_side A B C D" using oppositeside_b[OF `bet A M D` `col B C M` `\<not> col B C A`] .
	have "ang_eq A B C B C D" using Prop29B[OF `parallel A B C D` `oppo_side A B C D`] .
	have "\<not> (col B C D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B C D))"
hence "col B C D" by blast
		have "col C D B" using collinearorder[OF `col B C D`] by blast
		have "B = B" using equalityreflexiveE.
		have "col A B B" using collinear_b `B = B` by blast
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B B \<and> col C D B" using `A \<noteq> B` `C \<noteq> D` `col A B B` `col C D B` by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B B` `col C D B`] .
		have "\<not> (meets A B C D)" using parallel_f[OF `parallel A B C D`] by fastforce
		show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
	qed
	hence "\<not> col B C D" by blast
	have "ang_eq B C D D C B" using ABCequalsCBA[OF `\<not> col B C D`] .
	have "ang_eq A B C D C B" using equalanglestransitive[OF `ang_eq A B C B C D` `ang_eq B C D D C B`] .
	have "parallel A C B D" using `parallel A C B D` .
	have "bet A M D" using `bet A M D` .
	have "col C B M" using collinearorder[OF `col B C M`] by blast
	have "\<not> col C B A" using NCorder[OF `\<not> col B C A`] by blast
	have "oppo_side A C B D" using oppositeside_b[OF `bet A M D` `col C B M` `\<not> col C B A`] .
	have "ang_eq A C B C B D" using Prop29B[OF `parallel A C B D` `oppo_side A C B D`] .
	have "\<not> col A B C" using NCorder[OF `\<not> col B C A`] by blast
	have "ang_eq B C A A C B" using ABCequalsCBA[OF `\<not> col B C A`] .
	have "ang_eq B C A C B D" using equalanglestransitive[OF `ang_eq B C A A C B` `ang_eq A C B C B D`] .
	have "ang_eq A B C D C B" using `ang_eq A B C D C B` .
	have "triangle A B C" using triangle_b[OF `\<not> col A B C`] .
	have "\<not> col D C B" using equalanglesNC[OF `ang_eq A B C D C B`] .
	have "triangle D C B" using triangle_b[OF `\<not> col D C B`] .
	have "seg_eq B C C B" using equalityreverseE.
	have "seg_eq A B D C \<and> seg_eq A C D B \<and> ang_eq B A C C D B" using Prop26A[OF `triangle A B C` `triangle D C B` `ang_eq A B C D C B` `ang_eq B C A C B D` `seg_eq B C C B`] .
	have "seg_eq A B D C" using `seg_eq A B D C \<and> seg_eq A C D B \<and> ang_eq B A C C D B` by blast
	have "seg_eq A B C D" using congruenceflip[OF `seg_eq A B D C`] by blast
	have "seg_eq A C D B" using `seg_eq A B D C \<and> seg_eq A C D B \<and> ang_eq B A C C D B` by blast
	have "seg_eq A C B D" using congruenceflip[OF `seg_eq A C D B`] by blast
	have "seg_eq C A B D" using congruenceflip[OF `seg_eq A C B D`] by blast
	have "ang_eq B A C C D B" using `seg_eq A B D C \<and> seg_eq A C D B \<and> ang_eq B A C C D B` by blast
	have "seg_eq C B B C" using equalityreverseE.
	have "seg_eq C A B D \<and> seg_eq A B D C \<and> seg_eq C B B C" using `seg_eq C A B D` `seg_eq A B D C \<and> seg_eq A C D B \<and> ang_eq B A C C D B` `seg_eq C B B C` by blast
	have "\<not> col C A B" using NCorder[OF `\<not> col A B C`] by blast
	have "triangle C A B" using triangle_b[OF `\<not> col C A B`] .
	have "tri_cong C A B B D C" using trianglecongruence_b[OF `seg_eq C A B D` `seg_eq A B D C` `seg_eq C B B C` `triangle C A B`] .
	have "ang_eq C A B B D C" using equalanglesflip[OF `ang_eq B A C C D B`] .
	have "seg_eq A D D A" using equalityreverseE.
	have "A = A" using equalityreflexiveE.
	have "D = D" using equalityreflexiveE.
	have "A \<noteq> C" using angledistinct[OF `ang_eq A B C B C D`] by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `A \<noteq> C`] .
	have "C \<noteq> D" using angledistinct[OF `ang_eq A B C B C D`] by blast
	have "B \<noteq> A" using angledistinct[OF `ang_eq B A C C D B`] by blast
	have "D \<noteq> B" using angledistinct[OF `ang_eq A B C D C B`] by blast
	have "B \<noteq> D" using inequalitysymmetric[OF `D \<noteq> B`] .
	have "ray_on C A A" using ray4 `A = A` `C \<noteq> A` by blast
	have "ray_on C D D" using ray4 `D = D` `C \<noteq> D` by blast
	have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
	have "ray_on B D D" using ray4 `D = D` `B \<noteq> D` by blast
	have "seg_eq B A C D" using congruenceflip[OF `seg_eq A B C D`] by blast
	have "seg_eq C A B D" using congruenceflip[OF `seg_eq A C B D`] by blast
	have "seg_eq B D C A" using congruencesymmetric[OF `seg_eq C A B D`] .
	have "\<not> (col A B D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B D))"
hence "col A B D" by blast
		have "D = D" using equalityreflexiveE.
		have "col C D D" using collinear_b `D = D` by blast
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B D \<and> col C D D" using `A \<noteq> B` `C \<noteq> D` `col A B D` `col C D D` by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B D` `col C D D`] .
		show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
	qed
	hence "\<not> col A B D" by blast
	have "ang_eq A B D D C A" using equalangles_b[OF `ray_on B A A` `ray_on B D D` `ray_on C D D` `ray_on C A A` `seg_eq B A C D` `seg_eq B D C A` `seg_eq A D D A` `\<not> col A B D`] .
	have "seg_eq A B C D \<and> seg_eq A C B D \<and> ang_eq C A B B D C \<and> ang_eq A B D D C A \<and> tri_cong C A B B D C" using `seg_eq A B C D` `seg_eq A C B D` `ang_eq C A B B D C` `ang_eq A B D D C A` `tri_cong C A B B D C` by blast
	thus ?thesis by blast
qed

end