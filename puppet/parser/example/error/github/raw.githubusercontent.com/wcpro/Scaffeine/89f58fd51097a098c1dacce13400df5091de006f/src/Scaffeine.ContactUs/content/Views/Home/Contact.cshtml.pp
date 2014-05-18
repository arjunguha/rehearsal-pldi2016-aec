@{
    ViewBag.Title = "Contact Us";
}
@model $rootnamespace$.Models.ContactUsModel           
           
@section container
{
    <div class="container">
    <div class="row-fluid">
        <div class="page-header">
            <h1>
                Contact Us <small>A useful layout for forms</small></h1>
        </div>
    </div>
    <div class="row-fluid">
        <div class="span8">
            @using (Html.BeginForm("Contact", "Home", FormMethod.Post, new { @class = "form-horizontal" }))
            {
                @Html.ValidationSummary(true, "Password change was unsuccessful. Please correct the errors and try again.")
                <div>
                    <fieldset>
                        <div class="control-group">
                            <div class="control-label">
                                @Html.LabelFor(m => m.Name)
                            </div>
                            <div class="controls">
                                @Html.TextBoxFor(m => m.Name)
                                @Html.ValidationMessageFor(m => m.Name)
                            </div>
                        </div>
                        <div class="control-group">
                            <div class="control-label">
                                @Html.LabelFor(m => m.Email)
                            </div>
                            <div class="controls">
                                @Html.TextBoxFor(m => m.Email)
                                @Html.ValidationMessageFor(m => m.Email)
                            </div>
                        </div>
                        <div class="control-group warning">
                            <div class="control-label">
                                @Html.LabelFor(m => m.Message)
                            </div>
                            <div class="controls">
                                @Html.EditorFor(m => m.Message)
                                @Html.ValidationMessageFor(m => m.Message)
                            </div>
                        </div>
                        <div class="form-actions">
                            <input type="submit" value="Send Your Message" name="submit" id="submitButton" class="btn btn-primary"
                                title="Click here to submit your message!" />
                            <input type="reset" value="Clear Form" class="btn" title="Remove all the data from the form." />
                        </div>
                    </fieldset>
                </div>
            }
        </div>
        <div class="span4">            
            <address>
                <strong>Twitter, Inc.</strong><br>
                795 Folsom Ave, Suite 600<br>
                San Francisco, CA 94107<br>
                <abbr title="Phone">
                    P:</abbr>
                (123) 456-7890
            </address>
        </div>
    </div>
</div>

}

