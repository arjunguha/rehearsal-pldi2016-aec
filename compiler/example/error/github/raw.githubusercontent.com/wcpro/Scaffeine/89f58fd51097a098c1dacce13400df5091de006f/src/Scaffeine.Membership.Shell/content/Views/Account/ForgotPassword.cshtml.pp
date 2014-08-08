@model $rootnamespace$.Models.ForgotPasswordModel

@{
    ViewBag.Title = "Forgot Password";
}

<h2>Forgot Password</h2>
<p>
    Use the form below to change your password. 
</p>
<p>
    New passwords are required to be a minimum of @Membership.MinRequiredPasswordLength characters in length.
</p>



@using (Html.BeginForm())
{
    @Html.ValidationSummary(true, "Password change was unsuccessful. Please correct the errors and try again.")
    <div>
        <fieldset>
            <legend>Account Information</legend>

            <div class="editor-label">
                @Html.LabelFor(m => m.EmailAddress)
            </div>
            <div class="editor-field">
                @Html.TextBoxFor(m => m.EmailAddress)
                @Html.ValidationMessageFor(m => m.EmailAddress)
            </div>
            <div class="form-actions">
                <input type="submit" value="Retrieve Password" class="btn btn-primary" />
            </div>
        </fieldset>
    </div>
}