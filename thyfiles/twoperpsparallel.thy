theory twoperpsparallel
	imports n8_2 Euclid4 Geometry NCdistinct Prop28C betweennotequal collinearright inequalitysymmetric parallelflip parallelsymmetric ray4 rightangleNC
begin

theorem(in euclidean_geometry) twoperpsparallel:
	assumes 
		"ang_right A B C"
		"ang_right B C D"
		"same_side A D B C"
	shows "parallel A B C D"
proof -
	have "\<not> col A B C" using rightangleNC[OF `ang_right A B C`] .
	have "B \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
	obtain E where "bet B C E \<and> seg_eq C E B C" using extensionE[OF `B \<noteq> C` `B \<noteq> C`]  by  blast
	have "bet B C E" using `bet B C E \<and> seg_eq C E B C` by blast
	have "col B C E" using collinear_b `bet B C E \<and> seg_eq C E B C` by blast
	have "C \<noteq> E" using betweennotequal[OF `bet B C E`] by blast
	have "E \<noteq> C" using inequalitysymmetric[OF `C \<noteq> E`] .
	have "ang_right E C D" using collinearright[OF `ang_right B C D` `col B C E` `E \<noteq> C`] .
	have "ang_right D C E" using n8_2[OF `ang_right E C D`] .
	have "D = D" using equalityreflexiveE.
	have "\<not> col B C D" using rightangleNC[OF `ang_right B C D`] .
	have "C \<noteq> D" using NCdistinct[OF `\<not> col B C D`] by blast
	have "ray_on C D D" using ray4 `D = D` `C \<noteq> D` by blast
	have "supplement B C D D E" using supplement_b[OF `ray_on C D D` `bet B C E`] .
	have "ang_eq A B C B C D" using Euclid4[OF `ang_right A B C` `ang_right B C D`] .
	have "ang_eq B C D D C E" using Euclid4[OF `ang_right B C D` `ang_right D C E`] .
	have "ang_sum_right A B C B C D" using tworightangles_b[OF `supplement B C D D E` `ang_eq A B C B C D` `ang_eq B C D D C E`] .
	have "parallel B A C D" using Prop28C[OF `ang_sum_right A B C B C D` `same_side A D B C`] .
	have "parallel C D B A" using parallelsymmetric[OF `parallel B A C D`] .
	have "parallel C D A B" using parallelflip[OF `parallel C D B A`] by blast
	have "parallel A B C D" using parallelsymmetric[OF `parallel C D A B`] .
	thus ?thesis by blast
qed

end