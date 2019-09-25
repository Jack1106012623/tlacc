// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package util;

import java.io.File;


/**
 * Resolver for the name to file handle.
 *
 * LL comment: 24 July 2013: I believe that the only classes that implements this
 * are SimpleFileNameToStream, RCPNameToFileIStream, and RMIFilenameToStreamResolver.
 * I added the isStandardModule method.
 *
 * @author Leslie Lamport
 * @author Simon Zambrovski
 */
public interface FilenameToStream
{

	/*
	 * Higher layers of TLC (and the Toolbox) have to determine if a module was
	 * loaded from a library location s.a. those defined by TLA_LIBRARY (see
	 * SimpleFilenameToStream). Thus, capture this information at module load
	 * time when it is known where a module was loaded from.
	 */
	public static class TLAFile extends File {
		private final boolean isLibraryModule;

		public TLAFile(String pathname) {
			this(pathname, false);
		}

		public TLAFile(String pathname, boolean isLibraryModule) {
			super(pathname);
			this.isLibraryModule = isLibraryModule;
		}

		public TLAFile(String parent, String child) {
			super(parent, child);
			this.isLibraryModule = false;
		}

		public boolean isLibraryModule() {
			return isLibraryModule;
		}
	}
	
    /**
     * This method resolves the logical name to the OS-resource
     * @param filename
     * @param isModule
     * @return
     */
    public File resolve(String filename, boolean isModule);

      /**
       * August 2014 - TL
       * Added this method which returns all the path locations stored in the resolver
      */
    public String getFullPath();

    /**
     * Returns true iff moduleName is the name of a standard module, which
     * is identified by the directory in which its source file resides.
     *
     * @param moduleName
     * @return
	 * @see tla2sany.modanalyzer.ParseUnit.isLibraryModule()
	 * @see StandardModules.isDefinedInStandardModule()
     */
    public boolean isStandardModule(String moduleName) ;

	default boolean isLibraryModule(String moduleName) {
		return isStandardModule(moduleName);
	}
   
	static final String TMPDIR = System.getProperty("java.io.tmpdir");

	static boolean isInJar(final String aString) {
		return aString.startsWith("jar:") || aString.endsWith(".jar");
	}

	static boolean isArchive(String aString) {
		return isInJar(aString) || aString.endsWith(".zip");
	}
}
