theory squareflip
	imports n8_2 Geometry congruenceflip
begin

theorem(in euclidean_geometry) squareflip:
	assumes 
		"square A B C D"
	shows "square B A D C"
proof -
	have "seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A" using square_f[OF `square A B C D`] .
	have "seg_eq A B C D" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "seg_eq A B B C" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "seg_eq A B D A" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "ang_right D A B" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "ang_right A B C" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "ang_right B C D" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "ang_right C D A" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "seg_eq B A D C" using congruenceflip[OF `seg_eq A B C D`] by blast
	have "seg_eq B A A D" using congruenceflip[OF `seg_eq A B D A`] by blast
	have "seg_eq B A C B" using congruenceflip[OF `seg_eq A B B C`] by blast
	have "ang_right C B A" using n8_2[OF `ang_right A B C`] .
	have "ang_right B A D" using n8_2[OF `ang_right D A B`] .
	have "ang_right A D C" using n8_2[OF `ang_right C D A`] .
	have "ang_right D C B" using n8_2[OF `ang_right B C D`] .
	have "seg_eq B A D C \<and> seg_eq B A A D \<and> seg_eq B A C B \<and> ang_right C B A \<and> ang_right B A D \<and> ang_right A D C \<and> ang_right D C B" using `seg_eq B A D C` `seg_eq B A A D` `seg_eq B A C B` `ang_right C B A` `ang_right B A D` `ang_right A D C` `ang_right D C B` by blast
	have "square B A D C" using square_b[OF `seg_eq B A D C` `seg_eq B A A D` `seg_eq B A C B` `ang_right C B A` `ang_right B A D` `ang_right A D C` `ang_right D C B`] .
	thus ?thesis by blast
qed

end