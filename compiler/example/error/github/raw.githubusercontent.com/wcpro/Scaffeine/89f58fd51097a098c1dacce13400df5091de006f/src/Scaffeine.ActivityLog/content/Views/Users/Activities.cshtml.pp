@{
    ViewBag.Title = "User Details";
    Layout = "_AdminUserLayout.cshtml";
}

@model $rootnamespace$.Models.Users.UserActivitiesViewModel

<div class="tab-content">
    <div class="tab-pane active">
        
        <table class="table table-condensed table-striped">
            <thead>                
                <tr>
                    <td></td>
                </tr>
            </thead>
            <tbody>
                @foreach(var activity in Model.Activities)
                {
                    <tr>
                        <td>@activity.Activity</td>
                        <td>@activity.Created.Value.ToString()</td>                        
                    </tr>
                }
            </tbody>
        </table>

    </div>
</div>