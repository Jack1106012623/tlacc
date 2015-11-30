package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.ui.IEditorPart;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.ui.handler.OpenViewHandler;
import org.lamport.tla.toolbox.util.UIHelper;

public class OpenTLCErrorViewHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        Map<String, String> params = new HashMap<String, String>();
        params.put(OpenViewHandler.PARAM_VIEW_NAME, TLCErrorView.ID);
        UIHelper.runCommand(OpenViewHandler.COMMAND_ID, params);

        IEditorPart activeEditor = UIHelper.getActiveEditor();
        if (activeEditor != null)
        {
            if (activeEditor instanceof ModelEditor)
            {
                ModelEditor activeModelEditor = (ModelEditor) activeEditor;
                final Model model = activeModelEditor.getModel();
                if (model != null)
                {
                    UIHelper.runUISync(new Runnable() {

                        public void run()
                        {
                            TLCErrorView.updateErrorView(model);
                        }
                    });
                }
            }
        }

        return null;
    }

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (UIHelper.getActiveEditor() == null) {
			return false;
		}
		return super.isEnabled();
	}
}
