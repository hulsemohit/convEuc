theory rectanglerotate
	imports Geometry
begin

theorem(in euclidean_geometry) rectanglerotate:
	assumes 
		"rectangle A B C D"
	shows "rectangle B C D A"
proof -
	have "ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D" using rectangle_f[OF `rectangle A B C D`] .
	have "ang_right D A B" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "ang_right A B C" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "ang_right B C D" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "ang_right C D A" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "cross A C B D" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	obtain M where "bet A M C \<and> bet B M D" using cross_f[OF `cross A C B D`]  by  blast
	have "bet A M C" using `bet A M C \<and> bet B M D` by blast
	have "bet B M D" using `bet A M C \<and> bet B M D` by blast
	have "bet C M A" using betweennesssymmetryE[OF `bet A M C`] .
	have "cross B D C A" using cross_b[OF `bet B M D` `bet C M A`] .
	have "rectangle B C D A" using rectangle_b[OF `ang_right A B C` `ang_right B C D` `ang_right C D A` `ang_right D A B` `cross B D C A`] .
	thus ?thesis by blast
qed

end