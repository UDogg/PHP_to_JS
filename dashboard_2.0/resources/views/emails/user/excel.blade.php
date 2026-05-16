@component('mail::message')
# Hello ,

We are happy to inform you that your **Excel export is ready**.  
You can find the exported file attached with this email.

If you face any issues with the attachment, you can also download it directly using the button below.

@component('mail::button', ['url' => url('/storage/' . $filePath)])
Download Excel
@endcomponent

Thanks & Regards,  
{{ config('app.name') }}
@endcomponent


