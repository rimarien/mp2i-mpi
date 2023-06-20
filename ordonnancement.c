#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>
#include <assert.h>

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

void ps(process **ordonnanceur) {
  printf("PID CMD\n");
  if (*ordonnanceur == NULL) {return;}
  process *current = *ordonnanceur;
  do {
    printf("%d %s\n", current->actif->pid, current->actif->exec);
    current = current->suivant;
  } while (current != *ordonnanceur);
}

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

void delete(process *maillon) {
  assert(maillon->suivant != maillon && maillon->precedent != maillon);
  maillon->precedent->suivant = maillon->suivant;
  maillon->suivant->precedent = maillon->precedent;
  arrete(maillon->actif);
  free(maillon);
}

void delete_current(process **ordonnanceur) {
  assert(*ordonnanceur != NULL);
  process* current = *ordonnanceur;
  // S'il faut tuer le dernier processus
  if (current->suivant == current) {
    assert(current->precedent == current);
    arrete(current->actif);
    free(current);
    *ordonnanceur = NULL;
  } else {
    *ordonnanceur = current->suivant;
    delete(current);
  }
}

void kill(process **ordonnanceur, int pid) {

  if (*ordonnanceur == NULL) {return;}

  process* current = *ordonnanceur;

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

void killall(process **ordonnanceur, char* exec) {

  if (*ordonnanceur == NULL) {return;}

  process* current = (*ordonnanceur)->suivant;
  while (current != (*ordonnanceur)) {
    process* next = current->suivant;
    if (strcmp(current->actif->exec, exec) == 0) {
      delete(current);
    }
    current = next;
  }
  assert(current == *ordonnanceur);
  if (strcmp(current->actif->exec, exec) == 0) {
    delete_current(ordonnanceur);
  }

}

void cpu_quantum(processus *p) {

  assert(p != NULL);

  // Fait tourner fictivement le processus p

  return;
}

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