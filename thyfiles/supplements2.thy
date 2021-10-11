theory supplements2
	imports Geometry equalanglessymmetric equalanglestransitive supplements
begin

theorem(in euclidean_geometry) supplements2:
	assumes 
		"ang_sum_right A B C P Q R"
		"ang_eq A B C J K L"
		"ang_sum_right J K L D E F"
	shows "ang_eq P Q R D E F \<and> ang_eq D E F P Q R"
proof -
	obtain a b c d e where "supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq P Q R d b e" using tworightangles_f[OF `ang_sum_right A B C P Q R`]  by  blast
	obtain j k l m n where "supplement j k l m n \<and> ang_eq J K L j k l \<and> ang_eq D E F m k n" using tworightangles_f[OF `ang_sum_right J K L D E F`]  by  blast
	have "supplement a b c d e" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq P Q R d b e` by blast
	have "ang_eq A B C a b c" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq P Q R d b e` by blast
	have "ang_eq P Q R d b e" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq P Q R d b e` by blast
	have "supplement j k l m n" using `supplement j k l m n \<and> ang_eq J K L j k l \<and> ang_eq D E F m k n` by blast
	have "ang_eq J K L j k l" using `supplement j k l m n \<and> ang_eq J K L j k l \<and> ang_eq D E F m k n` by blast
	have "ang_eq D E F m k n" using `supplement j k l m n \<and> ang_eq J K L j k l \<and> ang_eq D E F m k n` by blast
	have "ang_eq a b c A B C" using equalanglessymmetric[OF `ang_eq A B C a b c`] .
	have "ang_eq a b c J K L" using equalanglestransitive[OF `ang_eq a b c A B C` `ang_eq A B C J K L`] .
	have "ang_eq a b c j k l" using equalanglestransitive[OF `ang_eq a b c J K L` `ang_eq J K L j k l`] .
	have "ang_eq d b e m k n" using supplements[OF `ang_eq a b c j k l` `supplement a b c d e` `supplement j k l m n`] .
	have "ang_eq P Q R m k n" using equalanglestransitive[OF `ang_eq P Q R d b e` `ang_eq d b e m k n`] .
	have "ang_eq m k n D E F" using equalanglessymmetric[OF `ang_eq D E F m k n`] .
	have "ang_eq P Q R D E F" using equalanglestransitive[OF `ang_eq P Q R m k n` `ang_eq m k n D E F`] .
	have "ang_eq D E F P Q R" using equalanglessymmetric[OF `ang_eq P Q R D E F`] .
	have "ang_eq P Q R D E F \<and> ang_eq D E F P Q R" using `ang_eq P Q R D E F` `ang_eq D E F P Q R` by blast
	thus ?thesis by blast
qed

end