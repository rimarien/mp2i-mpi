#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>
#include <time.h>

struct processus {
  char *exec;
  int pid;
};

typedef struct processus processus;

struct process {
  processus *actif;
  struct process *suivant;
  struct process *precedent;
};

typedef struct process process;


processus *lance_processus(char *exec) {

  // Variable allouée une fois pour tout en tout début de programme et
  // partagée par tous les appels, grâce au mot-clé `static` [HP]
  static int next_pid = 0;

  processus* p = malloc(sizeof(processus));

  // On va copier le nom, être responsable de libérer la mémoire
  // allouée mais pas celle du pointeur passé en paramètre
  p->exec = malloc(1 + strlen(exec));
  strcpy(p->exec, exec);
  p->pid = next_pid;
  next_pid++;

  // Lancement fictif du processus
  printf("* Lancement du processus %s\n", p->exec);

  return p;

}

// Comportement aléatoire juste pour tester
bool est_fini(processus *p) {
  assert (p != NULL);  // Surtout pour ignorer l'avertissement
  if (rand() % 10 == 0) {
    return true;
  } else {
    return false;
  }
}

void arrete(processus *p) {

  // Arrêt fictif du processus
  printf("* Arrêt du processus %s\n", p->exec);

  free(p->exec);
  free(p);

}

void cpu_quantum(processus *p) {

  assert(p != NULL);

  // Fait tourner fictivement le processus p

  return;
}

/*fonction void ps(process **ordonnanceur) qui affiche la liste
des processus (avec leur identifiant et leur nom*/

void ps(process **ordonnanceur) {
  printf("PID CMD\n");
  if (*ordonnanceur == NULL) {return;}
  process *current = *ordonnanceur;
   while (current != *ordonnanceur){
    printf("%d %s\n", current->actif->pid, current->actif->exec);
    current = current->suivant;
  }
}

/*fonction void ajoute_process(process **ordonnanceur,
processus *p) qui ajoute un nouveau processus *p dans la file d’attente
d’un ordonnanceur *ordonnanceur. Ce nouveau processus doit être ajouté
à la fin de la file pour ne pas doubler les processus existants*/

void ajoute_process(process **ordonnanceur, processus *p) {
  assert (p != NULL);
  process* maillon = malloc(sizeof(process));
  maillon->actif = p;
  if (*ordonnanceur == NULL) {
    maillon->suivant = maillon;
    maillon->precedent = maillon;
    *ordonnanceur = maillon;
  } else {
    process* last = (*ordonnanceur)->precedent;
    maillon->suivant = *ordonnanceur;
    maillon->precedent = last;
    last->suivant = maillon;
    (*ordonnanceur)->precedent = maillon;
  }
}

/* fonction void delete(process *maillon) qui supprime un ma-
illon de la file des processus et qui arrête le processus correspondant. On sup-
pose ici que ce maillon n’est pas celui pointé par l’ordonnanceur (et donc qu’il y
a moins un autre maillon)*/

void delete(process *maillon){
  process *precedent = maillon->precedent;
  process *suivant = maillon->suivant;
  precedent->suivant = suivant;
  suivant->precedent = precedent;
  arrete(maillon->actif);
  free(maillon);
}

/*fonction void delete_current(process **ordonnanceur)
qui supprime le maillon pointé par l’ordonnanceur. On suppose que ce maillon
existe et donc qu’il y a au moins un processus dans la file (mais pas nécessaire-
ment plusieurs).*/

void delete_current(process **ordonnanceur){
  process *current = *ordonnanceur;
  if (current->suivant = current)
  {
    arrete(current->actif);
    free(current);
    *ordonnanceur = NULL;
  }else
  {
    *ordonnanceur = current->suivant;
    delete(current);
  }
  
  
}

/* fonction void kill(process **ordonnanceur, int pid) qui
arrête le processus d’identifiant pid, s’il existe, en n’oubliant pas de le retirer
de la liste des processus*/

void kill(process **ordonnanceur, int pid){
  process *current = *ordonnanceur;

  int id_start = current->actif->pid;
  if (current->actif->pid == pid) {
    delete_current(ordonnanceur);
    return;
  }
  current = current->suivant;
  while (current != (*ordonnanceur)) {
    if (current->actif->pid == pid) {
      delete(current);
      return;
    }
    current = current->suivant;
  }
}

/*fonction de prototype void killall(process **ordonnanceur,
char* exec) qui arrête tous les processus de nom exec, s’il en existe*/

void killall(process **ordonnanceur, char* exec){
  process* current = (*ordonnanceur);
  while (current != *ordonnanceur)
  {
    process *next = current->suivant;
    if (strcmp(current->actif->exec, exec)==0)
    {
      delete(current);
    }
    current = next;
  }
  if (strcmp(current->actif->exec, exec)==0)
  {
    delete_current (ordonnanceur);
  }
}

/*fonction void round_robin(process **ordonnanceur) qui
simule l’algorithme de ROUND-ROBIN, c’est-à-dire qui prend
en paramètre un pointeur sur un ordonnanceur et qui alloue successivement et
dans l’ordre un quantum de temps à chaque processus de la file d’attente, tant
qu’il y a des processus dans la file. Un processus qui a terminé doit être arrêté
et sorti de la file*/


void round_robin(process **ordonnanceur) {
  printf("Round-robin en action !\n");
  while (*ordonnanceur != NULL) {
    processus *actif = (*ordonnanceur)->actif;
    printf("* Un quantum pour %d (%s)\n", actif->pid, actif->exec);
    cpu_quantum(actif);
    if (est_fini(actif)) {
      printf("* %d (%s) est terminé\n", actif->pid, actif->exec);
      delete_current(ordonnanceur);
    }
    if (*ordonnanceur != NULL) {
      *ordonnanceur = (*ordonnanceur)->suivant;
    }
  }
}

int main(void) {

  srand(time(NULL));

  process *ordo = NULL;
  ajoute_process(&ordo, lance_processus("gcc"));
  ajoute_process(&ordo, lance_processus("gcc"));
  ajoute_process(&ordo, lance_processus("jupyter"));
  ajoute_process(&ordo, lance_processus("emacs"));
  ajoute_process(&ordo, lance_processus("date"));
  ajoute_process(&ordo, lance_processus("date"));
  ajoute_process(&ordo, lance_processus("firefox"));
  ajoute_process(&ordo, lance_processus("ls"));
  ajoute_process(&ordo, lance_processus("firefox"));
  ajoute_process(&ordo, lance_processus("ls"));
  ps(&ordo);
  round_robin(&ordo);
  ps(&ordo);
  /* kill(&ordo, 3); */
  /* kill(&ordo, 4); */
  /* killall(&ordo, "firefox"); */
  /* killall(&ordo, "gcc"); */
  /* kill(&ordo, 2); */
  /* killall(&ordo, "date"); */
  /* killall(&ordo, "ls"); */
  /* /\* kill(&ordo, 4); *\/ */
  /* /\* kill(&ordo, 0); *\/ */
  /* /\* kill(&ordo, 1); *\/ */
  /* /\* kill(&ordo, 4); *\/ */
  /* /\* kill(&ordo, 5); *\/ */
  /* /\* kill(&ordo, 2); *\/ */
  /* /\* kill(&ordo, 2); *\/ */
  /* ps(ordo); */

}
