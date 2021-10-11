theory RTcongruence
	imports Geometry equalanglessymmetric equalanglestransitive
begin

theorem(in euclidean_geometry) RTcongruence:
	assumes 
		"ang_sum_right A B C D E F"
		"ang_eq A B C P Q R"
	shows "ang_sum_right P Q R D E F"
proof -
	obtain a b c d e where "supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e" using tworightangles_f[OF `ang_sum_right A B C D E F`]  by  blast
	have "supplement a b c d e" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_eq A B C a b c" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_eq D E F d b e" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_eq P Q R A B C" using equalanglessymmetric[OF `ang_eq A B C P Q R`] .
	have "ang_eq P Q R a b c" using equalanglestransitive[OF `ang_eq P Q R A B C` `ang_eq A B C a b c`] .
	have "supplement a b c d e \<and> ang_eq P Q R a b c \<and> ang_eq D E F d b e" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` `ang_eq P Q R a b c` `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_sum_right P Q R D E F" using tworightangles_b[OF `supplement a b c d e` `ang_eq P Q R a b c` `ang_eq D E F d b e`] .
	thus ?thesis by blast
qed

end