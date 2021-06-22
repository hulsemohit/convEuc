theory supplements2
	imports Axioms Definitions Theorems
begin

theorem supplements2:
	assumes: `axioms`
		"ang_suppl A B C P Q R"
		"ang_eq A B C J K L"
		"ang_suppl J K L D E F"
	shows: "ang_eq P Q R D E F \<and> ang_eq D E F P Q R"
proof -
	obtain a b c d e where "linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq P Q R d b e" using tworightangles_f[OF `axioms` `ang_suppl A B C P Q R`] by blast
	obtain j k l m n where "linear_pair j k l m n \<and> ang_eq J K L j k l \<and> ang_eq D E F m k n" using tworightangles_f[OF `axioms` `ang_suppl J K L D E F`] by blast
	have "linear_pair a b c d e" using `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq P Q R d b e` by blast
	have "ang_eq A B C a b c" using `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq P Q R d b e` by blast
	have "ang_eq P Q R d b e" using `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq P Q R d b e` by blast
	have "linear_pair j k l m n" using `linear_pair j k l m n \<and> ang_eq J K L j k l \<and> ang_eq D E F m k n` by blast
	have "ang_eq J K L j k l" using `linear_pair j k l m n \<and> ang_eq J K L j k l \<and> ang_eq D E F m k n` by blast
	have "ang_eq D E F m k n" using `linear_pair j k l m n \<and> ang_eq J K L j k l \<and> ang_eq D E F m k n` by blast
	have "ang_eq a b c A B C" using equalanglessymmetric[OF `axioms` `ang_eq A B C a b c`] .
	have "ang_eq a b c J K L" using equalanglestransitive[OF `axioms` `ang_eq a b c A B C` `ang_eq A B C J K L`] .
	have "ang_eq a b c j k l" using equalanglestransitive[OF `axioms` `ang_eq a b c J K L` `ang_eq J K L j k l`] .
	have "ang_eq d b e m k n" using supplements[OF `axioms` `ang_eq a b c j k l` `linear_pair a b c d e` `linear_pair j k l m n`] .
	have "ang_eq P Q R m k n" using equalanglestransitive[OF `axioms` `ang_eq P Q R d b e` `ang_eq d b e m k n`] .
	have "ang_eq m k n D E F" using equalanglessymmetric[OF `axioms` `ang_eq D E F m k n`] .
	have "ang_eq P Q R D E F" using equalanglestransitive[OF `axioms` `ang_eq P Q R m k n` `ang_eq m k n D E F`] .
	have "ang_eq D E F P Q R" using equalanglessymmetric[OF `axioms` `ang_eq P Q R D E F`] .
	have "ang_eq P Q R D E F \<and> ang_eq D E F P Q R" using `ang_eq P Q R D E F` `ang_eq D E F P Q R` by blast
	thus ?thesis by blast
qed

end