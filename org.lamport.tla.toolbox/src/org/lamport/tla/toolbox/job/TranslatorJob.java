package org.lamport.tla.toolbox.job;

import java.lang.reflect.InvocationTargetException;
import java.util.List;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

import pcal.TLAtoPCalMapping;
import pcal.Translator;

/**
 * Runs the PCal translator
 * @author Simon Zambrovski
 */
public class TranslatorJob extends WorkspaceJob
{
    private Translator translator;
    private Vector<String> callParams;
    private IResource fileToBuild;

    /**
     * @param name
     */
    public TranslatorJob(IResource fileToBuild)
    {
        super("PCal Translation");
        this.translator = new Translator();
        this.fileToBuild = fileToBuild;
        this.callParams = new Vector<String>();

        Activator.getDefault().logDebug("Translating " + fileToBuild.getLocation().toOSString());

        boolean hasPcalAlg = false;
        String[] params;
        Object prop;

        try
        {
            prop = fileToBuild
                    .getSessionProperty(ResourceHelper.getQName(IPreferenceConstants.CONTAINS_PCAL_ALGORITHM));
            if (prop != null)
            {
                hasPcalAlg = ((Boolean) prop).booleanValue();
            }

            IPreferenceStore projectPreferenceStore = PreferenceStoreHelper.getProjectPreferenceStore(fileToBuild
                    .getProject());

            String paramString = projectPreferenceStore.getString(IPreferenceConstants.PCAL_CAL_PARAMS);

            if (paramString != null)
            {
                params = paramString.split(" ");
            } else
            {
                params = new String[0];
            }

        } catch (CoreException e1)
        {
            Activator.getDefault().logError("Error reading parameters", e1);
            params = new String[0];
        }

        if (!hasPcalAlg)
        {
            // no algorithm detected
            Activator.getDefault().logDebug("No algorithm found");
        } else
        {
            Activator.getDefault().logDebug("Algorithm found");
        }

        // add params from the resource setting
        for (int i = 0; i < params.length; i++)
        {
            if (params[i] != null && !params[i].equals(""))
            {
                callParams.add(params[i]);
            }
        }
        callParams.add(fileToBuild.getLocation().toOSString());

    }

    /**
     * @see org.eclipse.core.resources.WorkspaceJob#runInWorkspace(org.eclipse.core.runtime.IProgressMonitor)
     */
    public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException
    {
        monitor.beginTask("PCal Translation", IProgressMonitor.UNKNOWN);

        // remove markers
        monitor.setTaskName("Removing problem markers");
        TLAMarkerHelper
                .removeProblemMarkers(fileToBuild, monitor, TLAMarkerHelper.TOOLBOX_MARKERS_TRANSLATOR_MARKER_ID);

        StringBuffer buffer = new StringBuffer();
        for (int i = 0; i < callParams.size(); i++)
        {
            buffer.append(" " + callParams.elementAt(i));
        }
        Activator.getDefault().logDebug("Translator invoked with params: '" + buffer.toString() + "'");

        TLAtoPCalMapping mapping = translator.runTranslation((String[]) callParams.toArray(new String[callParams.size()]));
		// If no mapping has been created (e.g. due to a parsing error), the
		// mapping object will be null. In this case we don't invalidate the old
		// mapping.
		if (mapping != null) {
			/*
			 * At this point, fileToBuild.getName() returns the simple name of
			 * the file--e.g., "Test.tla".
			 */
			Spec currentSpec = Activator.getSpecManager().getSpecLoaded();
			currentSpec.setTpMapping(mapping, fileToBuild.getName(), monitor);
		}
         
        monitor.worked(1);
        monitor.setTaskName("Analyzing results");

        List<String> errors = translator.getErrorMessages();

        if (errors.size() > 0)
        {
            monitor.setTaskName("Installing problem markers");
            for (int i = 0; i < errors.size(); i++)
            {
                String errorMessage = errors.get(i);

                TLAMarkerHelper.installProblemMarker(fileToBuild, fileToBuild.getName(), IMarker.SEVERITY_ERROR,
                        detectLocation(errorMessage), errorMessage, monitor,
                        TLAMarkerHelper.TOOLBOX_MARKERS_TRANSLATOR_MARKER_ID);
            }
        }

        monitor.worked(1);
        monitor.done();
        return Status.OK_STATUS;
    }

    /**
     * Return as runnable instead of the job
     * @param fileToBuild
     * @return
     */
    public static IRunnableWithProgress getAsRunnableWithProgress(final IResource fileToBuild)
    {
        final TranslatorJob job = new TranslatorJob(fileToBuild);
        return new IRunnableWithProgress() {
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException
            {
                try
                {
                    job.setRule(ResourceHelper.getModifyRule(fileToBuild));
                    job.runInWorkspace(monitor);
                } catch (CoreException e)
                {
                    throw new InvocationTargetException(e);
                }
            }
        };
    }

    private static int[] detectLocation(String message)
    {
        String LINE = "line ";
        String COLUMN = ", column ";

        int lineStarts = message.indexOf(LINE);
        int lineEnds = message.indexOf(COLUMN);
        if (lineStarts != -1 && lineEnds != -1)
        {
            String line = message.substring(lineStarts + LINE.length(), lineEnds);
            /*
             * afterColumnString is the substring of message that comes after the
             * first occurance of ", column" in message.
             */
            String afterColumnString = message.substring(lineEnds + COLUMN.length());
            // match any number of white spaces followed by the first string of digits.
            Matcher matcher = Pattern.compile("\\s*\\d+").matcher(afterColumnString);
            Assert.isTrue(matcher.find(), "No column number found in PlusCal message " + message);
            // the column string that should be a parsable int
            String column = matcher.group().trim();

            int lineNumber = -1;
            int columnNumber = -1;
            try
            {
                lineNumber = Integer.parseInt(line);
            } catch (NumberFormatException e)
            {
            }
            try
            {
                columnNumber = Integer.parseInt(column);
            } catch (NumberFormatException e)
            {
            }
            return new int[] { lineNumber, columnNumber, lineNumber, columnNumber + 1 };
        }
        return new int[] { -1, -1, -1, -1 };
    }
}
