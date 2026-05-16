<?php

namespace Database\Seeders;

use App\Models\EmailTemplate;
use Illuminate\Database\Console\Seeds\WithoutModelEvents;
use Illuminate\Database\Seeder;

class RaiseQueryEmailTemplateSeeder extends Seeder
{
    /**
     * Run the database seeds.
     */
    public function run(): void
    {
        $templates = [
            [
                'stage' => 'Quote',
                'subject' => 'WH-Karoinsure-Quote Page Query: "WH-Karoinsure-Query Regarding Quote Request"',
                'body' => <<<EOD
                Dear Karoinsure Team,

                I am writing to request urgent assistance regarding a Quote Page query. Here are the relevant details:

                Topic: {topic}  
                Trace ID: {trace_id}  
                Registration Number / RTO: {registration_number}  
                Insurance Company: {insurance_company}  
                Related To: {related_to}  
                My User ID: {user_id}  

                I would appreciate your prompt attention to this matter.

                Sincerely,  
                {name} ({email})

                <b>Note: If you have any further questions, please call us at +91 7861969699.</b>
                EOD
            ],
            [
                'stage' => 'Proposal Pending',
                'subject' =>  'WH-Proposal Pending: "WH-Karoinsure-Proposal Query"',
                'body' => <<<EOD
                Dear Karoinsure Team,

                I am writing to request urgent assistance regarding a Quote Page query. Here are the relevant details:

                Topic: {topic}
                Customer Name: {customer_name}  
                Proposal Number: {proposal_number}  
                Trace ID: {trace_id}  
                Insurance Company: {insurance_company}  
                Registration Number / RTO: {registration_number}  
                Related To: {related_to}  
                My User ID: {user_id}

                I would appreciate your prompt attention to this matter.

                Sincerely,  
                {name} ({email})

                <b>Note: If you have any further questions, please call us at +91 7861969699.</b>
                EOD
            ],
            [
                'stage' => 'Inspection',
                'subject' => 'WH-Inspection: "WH-Karoinsure-Inspection Query"',
                'body' => <<<EOD
                    Dear Karoinsure Team,

                    I am writing to request urgent assistance regarding a Quote Page query. Here are the relevant details:

                    Topic: {topic}  
                    Customer Name: {customer_name}  
                    Proposal Number: {proposal_number}  
                    Trace ID: {trace_id}  
                    Insurance Company: {insurance_company}  
                    Inspection Number: {inspection_number}  
                    Registration Number: {registration_no} / RTO  
                    Related To: {related_to}  
                    My User ID: {user_id}  

                    I would appreciate your prompt attention to this matter.

                    Sincerely,  
                    {name} ({email})

                    <b>Note: If you have any further questions, please call us at +91 7861969699.</b>
                    EOD
            ],
            [
                'stage' => 'Payment Pending',
                'subject' => 'WH-Payment Pending: "WH-Karoinsure-Payment Pending Query"',
                'body' => <<<EOD
                Dear Karoinsure Team,

                I am writing to request urgent assistance regarding a Quote Page query. Here are the relevant details:

                Topic: {topic}  
                Customer Name: {customer_name}  
                Proposal Number: {proposal_number}  
                Trace ID: {trace_id}  
                Insurance Company: {insurance_company}  
                Inspection Number: {inspection_number}  
                Registration Number: {registration_no} / RTO  
                Related To: {related_to}  
                My User ID: {user_id}  
                Transaction Stage: Not necessary

                I would appreciate your prompt attention to this matter.

                Sincerely,  
                {name} ({email})

                <b>Note: If you have any further questions, please call us at +91 7861969699.</b>
                EOD
            ],
            [
                'stage' => 'Booking',
                'subject' => 'WH-Booking Pending: "WH-Karoinsure-Booking Pending Query"',
                'body' => <<<EOD
            Dear Karoinsure Team,

            I am writing to request urgent assistance regarding a Quote Page query. Here are the relevant details:

            Topic: {topic}  
            Customer Name: {customer_name}  
            Proposal Number: {proposal_number}  
            Trace ID: {trace_id}  
            Insurance Company: {insurance_company}  
            Inspection Number: {inspection_number}  
            Registration Number: {registration_no} / RTO  
            Related To: {related_to}  
            Transaction Number: {transaction_number}  
            Policy Number: {policy_number}  
            My User ID: {user_id}  

            I would appreciate your prompt attention to this matter.

            Sincerely,  
            {name} ({email})

            <b>Note: If you have any further questions, please call us at +91 7861969699.</b>
            EOD
            ],
            [
                'stage' => 'Issued',
                'subject' => 'WH-Issued Policy: "WH-Karoinsure-Issued Policy PDF Query"',
                'body' => <<<EOD
            Dear Karoinsure Team,

            I am writing to request urgent assistance regarding a Quote Page query. Here are the relevant details:

            Topic: {topic}  
            Customer Name: {customer_name}  
            Proposal Number: {proposal_number}  
            Trace ID: {trace_id}  
            Insurance Company: {insurance_company}  
            Inspection Number: {inspection_number}  
            Registration Number: {registration_no} / RTO  
            Related To: {related_to}  
            Transaction Number: {transaction_number}  
            Policy Number: {policy_number}  
            My User ID: {user_id}  

            I would appreciate your prompt attention to this matter.

            Sincerely,  
            {name} ({email})

            <b>Note: If you have any further questions, please call us at +91 7861969699.</b>
            EOD
            ]
            // Similarly add "inspection", "payment_pending", "booking_pending", "issued_policy"
        ];

        EmailTemplate::insert($templates);
    }
}
